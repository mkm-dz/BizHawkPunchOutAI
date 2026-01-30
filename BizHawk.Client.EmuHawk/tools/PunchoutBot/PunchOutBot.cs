using System;
using System.Collections.Generic;
using System.Drawing;
using System.IO;
using System.Net;
using System.Net.Sockets;
using System.Linq;
using System.Text;
using Newtonsoft.Json;
using System.Threading;


using System.Windows.Forms;


using BizHawk.Client.EmuHawk.ToolExtensions;

using BizHawk.Emulation.Common;
using BizHawk.Client.Common;
using System.Threading.Tasks;
using System.Globalization;

namespace BizHawk.Client.EmuHawk
{
	public partial class PunchOutBot : ToolFormBase, IToolFormAutoConfig
	{
		private const string DialogTitle = "PunchOut Bot";

		private string _currentFileName = string.Empty;
		private const string serverAddress = "127.0.0.1";
		private const int clientPort = 9999;
		private const int serverPort = 9998;
		private string _trigger = String.Empty;
		private bool _allowScreenshots = false;
		private static readonly JsonSerializerSettings _jsonSettings = new JsonSerializerSettings();

		private int framesPerCommand = 40;
		private int currentFrameCounter = 0;
		private int lastTimingDelay = 0;
		private bool inMainLoop = false;
		private bool waitingForOpponentActionToEnd = false;
		private bool onReset = false;
		private int scoreContext = 0;

		private TextInfo capitalize = new CultureInfo("en-US", false).TextInfo;


		private string CurrentFileName
		{
			get { return _currentFileName; }
			set
			{
				_currentFileName = value;

				if (!string.IsNullOrWhiteSpace(_currentFileName))
				{
					Text = DialogTitle + " - " + Path.GetFileNameWithoutExtension(_currentFileName);
				}
				else
				{
					Text = DialogTitle;
				}
			}

		}

		private bool _isBotting = false;
		private object commandSync = new object();
		private ControllerCommand commandInQueue = null;

		private bool _replayMode = false;
		private string _lastRom = "";

		private bool commandInQueueAvailable = false;

		private MemoryDomain _currentDomain;
		private bool _bigEndian;
		private int _dataSize;

		private int _wins = 0;
		private int _losses = 0;
		private int _p2_wins = 0;
		private int _p2_losses = 0;
		private string _lastResult = "Unknown";
		private float _winsToLosses = 0;
		private float _p2_winsToLosses = 0;
		private int _totalGames = 0;
		private int _OSDMessageTimeInSeconds = 6;
		private int _post_round_wait_time = 0;
		private bool sendStateToServer = false;
		public bool game_in_progress = false;

		private ILogEntryGenerator _logGenerator;
		private TcpServer server;
		
		// Persistent connection to Python server for state transmission
		private TcpClient _persistentClient = null;
		private NetworkStream _persistentStream = null;
		private readonly object _connectionLock = new object();

		#region Services and Settings

		[RequiredService]
		private IEmulator Emulator { get; set; }

		// Unused, due to the use of MainForm to loadstate, but this needs to be kept here in order to establish an IStatable dependency
		[RequiredService]
		private IStatable StatableCore { get; set; }

		[RequiredService]
		private IMemoryDomains MemoryDomains { get; set; }

		[ConfigPersist]
		public PunchOutBotSettings Settings { get; set; }

		public class PunchOutBotSettings
		{
			public PunchOutBotSettings()
			{
				RecentBotFiles = new RecentFiles();
				TurboWhenBotting = true;
			}

			public RecentFiles RecentBotFiles { get; set; }
			public bool TurboWhenBotting { get; set; }
		}

		#endregion

		#region sockethandling
		private TcpClient CreateTCPClient(string IP, int port)
		{
			return new TcpClient(IP, port);
		}

		private Task CreateTcpServer(string IP, int port)
		{
			this.server = new TcpServer(IP, port);
			this.server.onMessageReceived += TcpServer_onMessageReceived;

			return Task.Factory.StartNew(() =>
			{
				this.server.LoopClients();
			});
		}

		private void TcpServer_onMessageReceived(string message)
		{
			if (string.IsNullOrEmpty(message))
				return;

			ControllerCommand cc = new ControllerCommand();
			try
			{
				cc = JsonConvert.DeserializeObject<ControllerCommand>(message.ToString().ToLower());
				this.commandInQueue = cc;
				this.commandInQueueAvailable = true;
				GlobalWin.MainForm.UnpauseEmulator();
			}
			catch (ArgumentNullException ane)
			{
				cc.type = "__err__" + ane.ToString();
			}
			catch (SocketException se)
			{
				cc.type = "__err__" + se.ToString();
			}
			catch (Exception e)
			{
				cc.type = "__err__" + e.ToString();
			}
		}

		#endregion

		#region Initialize

		public PunchOutBot()
		{
			InitializeComponent();
			Text = DialogTitle;
			Settings = new PunchOutBotSettings();
		}

		private void PunchOutBot_Load(object sender, EventArgs e)
		{
			StartBot();
		}

		#endregion

		#region punchout

		public int GetOpponentId()
		{
			return _currentDomain.PeekByte(0x0001);
		}

		public int GetHealthP1()
		{
			return _currentDomain.PeekByte(0x0391);
		}

		public int GetHealthP2()
		{
			return _currentDomain.PeekByte(0x0398);
		}

		public int GetOpponentAction()
		{
			// This is how I think it is working
			// | 0x0039 | 0x003A | 0x003B  | 0x003C  |
			// | Counter| Offset | Ind.Ref1|Ind.Ref2 |
			//
			// Counter holds a value that when 0 (or other TBD values for specific characters) executes the action
			// Offset holds a value that offsets Ind.Ref1
			// Ind.Ref Hold references to the address who has the actual value of the actions
			//    In this case string memory address =  [Ind.Ref2] + [Ind.Ref1 + Offset]
			//    e.g 
			// | 0x0039 | 0x003A | 0x003B | 0x003C |
			// |    0   |    3   |   96   |   94   |
			// Memory address that contains the movement will be @ 0x9499
			int firstAddress = _currentDomain.PeekByte(0x003C);
			int secondAddress = _currentDomain.PeekByte(0x003B);
			int offset = _currentDomain.PeekByte(0x003A);

			secondAddress += offset;
			secondAddress += 1;

			string fullAddress = String.Format("0x{0}{1}", firstAddress.ToString("X2"), secondAddress.ToString("X2"));
			long actualAddress = Convert.ToInt64(fullAddress, 16);
			return _currentDomain.PeekByte(actualAddress);
		}

		public int GetOpponentActionTimer()
		{
			return _currentDomain.PeekByte(0x0039);
		}

		public bool IsRoundStarted()
		{
			if (_currentDomain.PeekByte(0x0004) == 255)
			{
				return true;
			}

			return false;
		}

		public int CanThrowPunches()
		{
			// 00BC Seems to track if you can throw punches or if you are blocked by an action
			// does not include  blinking pink
			if (_currentDomain.PeekByte(0x00BC) == 0)
				return 0;
			else
				return 1;
		}

		public int IsBlinkingPink()
		{
			// 048E Seems to track if you Mac is blinking pink but it also returns true when mac is hit.
			if(this.GetHearts() == 0)
			{
				return 1;
			}

			return 0;
		}

		public int GetStars()
		{
			return _currentDomain.PeekByte(0x0342);
		}

		public bool IsOpponentMovingInMemory()
		{
			if (_currentDomain.PeekByte(0x0097) != 0)
			{
				return true;
			}

			return false;
		}

		public bool IsMacMovingOnMemory()
		{

			if ((_currentDomain.PeekByte(0x0051) != 0))
			{
				return true;
			}

			return false;
		}

		public int GetBerserkerAction()
		{
			return _currentDomain.PeekByte(0x0035);
		}

		public bool IsMacInNeutralPosition()
		{
			// [Not 100% confirmed] But 1 seems to be standing and 2 standing in pink. Similar to the previous
			// one.
			if (_currentDomain.PeekByte(0x0050) == 1 || _currentDomain.PeekByte(0x0050) == 2)
			{
				return true;
			}

			return false;
		}

		private bool IsRoundOver()
		{
			if (!this.onReset)
			{
				return (GetHealthP1() <= 0 || GetHealthP2() <= 0 )|| _currentDomain.PeekByte(0x0004) != 255;
			}
			else
			{
				return false;
			}
		}

		private int GetScore()
		{
			byte units = _currentDomain.PeekByte(0x03EC);
			byte tens = _currentDomain.PeekByte(0x03EB);
			byte hundreds = _currentDomain.PeekByte(0x03EA);
			byte thousands = _currentDomain.PeekByte(0x03E9);
			string formatedString = string.Format("{0}{1}{2}{3}", thousands, hundreds, tens, units);
			int testc = Convert.ToInt32(formatedString);
			return testc;
		}

		private int GetHearts()
		{
			byte units = _currentDomain.PeekByte(0x0324);
			byte tens = _currentDomain.PeekByte(0x0323);

			string formatedString = string.Format("{0}{1}", tens, units);
			return Convert.ToInt32(formatedString);
		}

		private string GetRoundResult()
		{
			if (this.IsRoundOver())
			{
				if (this.GetHealthP2() > 0 && this.GetHealthP2() >= this.GetHealthP1())
				{
					// P2
					return "2";
				}
				else
				{
					// P1
					return "1";
				}
			}
			else
			{
				// NOT OVER
				return "3";
			}
		}

		public Dictionary<string, bool> GetJoypadButtons(int? controller = null)
		{
			var buttons = new Dictionary<string, bool>();
			var adaptor = Global.AutofireStickyXORAdapter;
			foreach (var button in adaptor.Source.Definition.BoolButtons)
			{
				if (!controller.HasValue)
				{
					buttons[button] = adaptor.IsPressed(button);
				}
				else if (button.Length >= 3 && button.Substring(0, 2) == "P" + controller)
				{
					buttons[button.Substring(3)] = adaptor.IsPressed("P" + controller + " " + button.Substring(3));
				}
			}
			return buttons;
		}

		public string SetJoypadButtons(Dictionary<string, bool> buttons, int? controller = null, bool clearAll = false)
		{
			StringBuilder pressed = new StringBuilder();
			try
			{
				foreach (var button in buttons.Keys)
				{
					var invert = false;
					bool? theValue;
					var theValueStr = buttons[button].ToString();

					if (!string.IsNullOrWhiteSpace(theValueStr) && !clearAll)
					{
						if (theValueStr.ToLower() == "false")
						{
							theValue = false;
						}
						else if (theValueStr.ToLower() == "true")
						{
							theValue = true;
						}
						else
						{
							invert = true;
							theValue = null;
						}
					}
					else
					{
						theValue = null;
					}

					var toPress = button.ToString();
					if (controller.HasValue)
					{
						toPress = "P" + controller + " " + this.capitalize.ToTitleCase(button);
					}

					if (!invert)
					{
						if (theValue.HasValue) // Force
						{
							Global.LuaAndAdaptor.SetButton(toPress, theValue.Value);
							if (theValue.Value)
							{
								pressed.Append(toPress + "|");
							}
							Global.ActiveController.Overrides(Global.LuaAndAdaptor);
						}
						else // Unset
						{
							Global.LuaAndAdaptor.UnSet(toPress);
							Global.ActiveController.Overrides(Global.LuaAndAdaptor);
						}
					}
					else // Inverse
					{
						Global.LuaAndAdaptor.SetInverse(toPress);
						Global.ActiveController.Overrides(Global.LuaAndAdaptor);
					}
				}
			}
			catch (Exception e)
			{
				throw;
				/*Eat it*/
			}
			return pressed.ToString();
		}
		private class PlayerState
		{
			public PlayerState()
			{
			}
			public int character { get; set; }
			public int health { get; set; }

			public int hearts { get; set; }

			public int score { get; set; }

			public Dictionary<string, bool> buttons { get; set; }

			public int action { get; set; }

			public int actionTimer { get; set; }

			public int blinkingPink { get; set; }

			public int bersekerAction { get; set; }

			public int stars { get; set; }

		}
		private class GameState
		{
			public GameState()
			{
			}
			public PlayerState p1 { get; set; }
			public PlayerState p2 { get; set; }
			public int frame { get; set; }
			public string result { get; set; }
			public bool round_started { get; set; }
			public bool round_over { get; set; }
		}

		private GameState GetCurrentState()
		{
			PlayerState p1 = new PlayerState();
			PlayerState p2 = new PlayerState();
			GameState gs = new GameState();
			p1.health = GetHealthP1();
			p1.action = 0;
			p1.buttons = GetJoypadButtons(1);
			p1.character = -1;
			p1.hearts = this.GetHearts();
			p1.score = this.GetScore();
			p1.blinkingPink = this.IsBlinkingPink();
			p1.bersekerAction= 0;
			p1.stars = this.GetStars();

			p2.health = this.GetHealthP2();
			p2.action = this.GetOpponentAction();
			p2.buttons = this.GetJoypadButtons(2);
			p2.actionTimer = this.GetOpponentActionTimer();
			p2.character = this.GetOpponentId();
			p2.blinkingPink = 0;
			p2.bersekerAction = this.GetBerserkerAction();
			p2.stars = 0;

			gs.p1 = p1;
			gs.p2 = p2;
			gs.result = GetRoundResult();
			gs.frame = Emulator.Frame;
			gs.round_started = this.IsRoundStarted();
			gs.round_over = this.IsRoundOver();

			return gs;
		}
		#endregion

		#region IToolForm Implementation

		public bool UpdateBefore { get { return true; } }

		public void NewUpdate(ToolFormUpdateType type) { }

		public void UpdateValues()
		{
			Update(fast: false);
		}

		public void FastUpdate()
		{
			Update(fast: true);
		}

		public void Restart()
		{
			if (_currentDomain == null ||
				MemoryDomains.Contains(_currentDomain))
			{
				_currentDomain = MemoryDomains.SystemBus;
				_bigEndian = _currentDomain.EndianType == MemoryDomain.Endian.Big;
				_dataSize = 1;
			}

			if (_isBotting)
			{
				StopBot();
			}


			if (_lastRom != GlobalWin.MainForm.CurrentlyOpenRom)
			{
				_lastRom = GlobalWin.MainForm.CurrentlyOpenRom;
				SetupControlsAndProperties();
			}
		}

		public bool AskSaveChanges()
		{
			return true;
		}

		#endregion

		#region Control Events

		#region FileMenu

		private void FileSubMenu_DropDownOpened(object sender, EventArgs e)
		{
		}


		private void ExitMenuItem_Click(object sender, EventArgs e)
		{
			Close();
		}

		#endregion

		#region Options Menu

		private void OptionsSubMenu_DropDownOpened(object sender, EventArgs e)
		{
			TurboWhileBottingMenuItem.Checked = Settings.TurboWhenBotting;
			BigEndianMenuItem.Checked = _bigEndian;
		}

		private void MemoryDomainsMenuItem_DropDownOpened(object sender, EventArgs e)
		{
			MemoryDomainsMenuItem.DropDownItems.Clear();
			MemoryDomainsMenuItem.DropDownItems.AddRange(
				MemoryDomains.MenuItems(SetMemoryDomain, _currentDomain.Name)
				.ToArray());
		}

		private void BigEndianMenuItem_Click(object sender, EventArgs e)
		{
			_bigEndian ^= true;
		}

		private void DataSizeMenuItem_DropDownOpened(object sender, EventArgs e)
		{
			_1ByteMenuItem.Checked = _dataSize == 1;
			_2ByteMenuItem.Checked = _dataSize == 2;
			_4ByteMenuItem.Checked = _dataSize == 4;
		}

		private void _1ByteMenuItem_Click(object sender, EventArgs e)
		{
			_dataSize = 1;
		}

		private void _2ByteMenuItem_Click(object sender, EventArgs e)
		{
			_dataSize = 2;
		}

		private void _4ByteMenuItem_Click(object sender, EventArgs e)
		{
			_dataSize = 4;
		}

		private void TurboWhileBottingMenuItem_Click(object sender, EventArgs e)
		{
			Settings.TurboWhenBotting ^= true;
		}

		#endregion

		private void RunBtn_Click(object sender, EventArgs e)
		{
			StartBot();
		}

		private void StopBtn_Click(object sender, EventArgs e)
		{
			StopBot();
		}






		private void ClearStatsContextMenuItem_Click(object sender, EventArgs e)
		{

		}

		#endregion

		#region Classes

		private class ControllerCommand
		{
			public ControllerCommand() { }
			public string type { get; set; }
			public string timing { get; set; }
			public Dictionary<string, bool> p1 { get; set; }
			public Dictionary<string, bool> p2 { get; set; }
			public string savegamepath { get; set; }

		}




		#endregion

		#region File Handling

		private void LoadFileFromRecent(string path)
		{
			var result = LoadBotFile(path);
			if (!result)
			{
				Settings.RecentBotFiles.HandleLoadError(path);
			}
		}

		private bool LoadBotFile(string path)
		{

			return true;
		}

		private void SaveBotFile(string path)
		{

		}

		#endregion

		private void SetupControlsAndProperties()
		{
			UpdateBotStatusIcon();
		}

		private void SetMemoryDomain(string name)
		{
			_currentDomain = MemoryDomains[name];
			_bigEndian = MemoryDomains[name].EndianType == MemoryDomain.Endian.Big;
		}

		private int GetRamvalue(int addr)
		{
			int val;
			switch (_dataSize)
			{
				default:
				case 1:
					val = _currentDomain.PeekByte(addr);
					break;
				case 2:
					val = _currentDomain.PeekUshort(addr, _bigEndian);
					break;
				case 4:
					val = (int)_currentDomain.PeekUint(addr, _bigEndian);
					break;
			}

			return val;
		}

		private void Update(bool fast)
		{
			// Every frame we assume we don't want to send our state unless somebody wants to during this iteration.
			this.sendStateToServer = false;

			// Reset has priority on everyframe
			this.ExecuteResetIfNeeded();

			// Resume a paused game has priority
			this.ResumeGameIfNeeded();

			this.InitializeMainLoop();

			this.HandleButtons();

			// [** Reviewing this logic **]
			// Reason is that currently Mac is "dumb", meaning it only reacts to server order and then returns the state.
			// This is in order to preserve (previous_state, next_state) dupla. Otherwise states need to be ordered.

			// We need to check if the opponent is attacking us.
			//this.HasOpponentStartedAnAttack();

			// If mac is idle we need to notify the server (who is prepared to listen everytime we send the state)
			// this.IsMacIdle();
			// [** End Reviewing this logic **]

			this.ResetLoopContext();

			if (this.sendStateToServer)
			{
				// send status to server.
				GameState gs = GetCurrentState();
				this.SendEmulatorGameStateToController(gs);
				this._trigger = String.Empty;
			}

		}

		private void ExecuteResetIfNeeded()
		{
			if (this.IsRoundOver())
			{
				// if the round is over we clear any message waiting on the agent.
				this.sendStateToServer = true;
				this._trigger += ", RoundOver";
			}

			if (this.commandInQueueAvailable && this.commandInQueue.type == "reset")
			{
				this.commandInQueueAvailable = false;

				// This is only for letting the server know we executed the command.
				this.sendStateToServer = true;
				this._trigger += ", ReceivedResetCommand";
				if (_isBotting)
				{
					try
					{
						if (IsRoundOver() && game_in_progress)
						{
							_post_round_wait_time--;
							game_in_progress = false;
							_totalGames = _totalGames + 1;
							if (GetRoundResult() == "1")
							{
								_wins = _wins + 1;
								_lastResult = "P1 Win";
								_p2_losses = _p2_losses + 1;

							}
							else
							{
								_losses = _losses + 1;
								_lastResult = "P1 Loss";
								_p2_wins = _p2_wins + 1;
							}

							_winsToLosses = (float)_wins / _totalGames;
							_p2_winsToLosses = (float)_p2_wins / _totalGames;
							GlobalWin.OSD.ClearGUIText();
							GlobalWin.OSD.AddMessageForTime("Game #: " + _totalGames + " | Last Result: " + _lastResult + " | P1 Wins-Losses: " + _wins + "-" + _losses + " (" + _winsToLosses + ") | P2 Wins-Losses: " + _p2_wins + "-" + _p2_losses + " (" + _p2_winsToLosses + ")", _OSDMessageTimeInSeconds);
						}
					}
					catch (Exception e)
					{
						throw e;
					}
				}
				game_in_progress = true;
				this.onReset = true;
				GlobalWin.MainForm.LoadState(this.commandInQueue.savegamepath, Path.GetFileName(this.commandInQueue.savegamepath));
			}
		}

		private void ResumeGameIfNeeded()
		{
			if (this.commandInQueueAvailable && this.commandInQueue.type == "resume")
			{
				GlobalWin.MainForm.UnpauseEmulator();
				this.commandInQueueAvailable = false;
			}
		}

		private void TakeScreenshot(GameState state)
		{
			if (!this._allowScreenshots)
			{
				return;
			}

			string message = String.Empty;
			if (this._trigger.Contains("FinishedPressingButtons"))
			{
				message = JsonConvert.SerializeObject(this.commandInQueue);
			}
			else
			{
				message = JsonConvert.SerializeObject(state);
			}
			GlobalWin.MainForm.TakeScreenshotWithMessage(String.Format("{0}\n\r{1}", this._trigger, message));
		}

		/// <summary>
		/// Verifies if Mac is required to execute an action or if any button pressing is needed
		/// </summary>
		private void InitializeMainLoop()
		{
			// After one action we do not need the reset flag
			this.onReset = false;

			if (this.inMainLoop)
			{
				this.currentFrameCounter++;
			}

			// If we have a pending command and we are not pressing the buttons, execute movement.
			if (this.commandInQueueAvailable && this.commandInQueue.type == "buttons")
			{
				this.commandInQueueAvailable = false;
				this.inMainLoop = true;
				this.lastTimingDelay = this.CalculateMoveStart();
			}
		}

		/// <summary>
		/// Executes Mac moves over an X amount of frames to guarantee the movement execution.
		/// it also marks the sendToServer flag as true so the execution outcome is reported.
		/// </summary>
		private void HandleButtons()
		{
			if ((this.currentFrameCounter == (this.framesPerCommand + this.lastTimingDelay)) && this.inMainLoop)
			{
				string buttonsPressed = SetJoypadButtons(this.commandInQueue.p1, 1);
				buttonsPressed += String.Format(" {0} f.", this.lastTimingDelay);
				GlobalWin.OSD.ClearGUIText();
				GlobalWin.OSD.AddMessageForTime(buttonsPressed, _OSDMessageTimeInSeconds);
				this.scoreContext = this.GetScore();
			}
		}

		private void ResetLoopContext()
		{
			if (this.currentFrameCounter > (this.framesPerCommand + this.lastTimingDelay) && this.inMainLoop)
			{
				this.currentFrameCounter = 0;
				this.inMainLoop = false;
				this.sendStateToServer = true;
				this.lastTimingDelay = 0;
				SetJoypadButtons(this.commandInQueue.p1, 1, true);
				this._trigger += ", FinishedPressingButtons";
			}
		}

		private int CalculateMoveStart()
		{
			if (this.commandInQueue.timing.ToLowerInvariant().Equals("low"))
			{
				return 5;
			}
			else if (this.commandInQueue.timing.ToLowerInvariant().Equals("medium"))
			{
				return 11;
			}
			else
			{
				return 18;
			}
		}

		/// <summary>
		/// Is Mac pressing any button or waiting to report the result of an action
		/// </summary>
		/// <returns>true if buttons are being pressed false otherwise</returns>
		private bool IsMacPressingButtons()
		{
			if (this.currentFrameCounter > 0)
			{
				return true;
			}

			return false;
		}

		/// <summary>
		/// Verifies if opponent has started an attack, this method considers only NEW attacks
		/// </summary>
		private void HasOpponentStartedAnAttack()
		{
			if (this.IsOpponentMovingInMemory() && this.waitingForOpponentActionToEnd == false)
			{
				this.waitingForOpponentActionToEnd = true;

				// We don't want to send an "started attack" when we are in the middle.
				if (this.commandInQueueAvailable == false && !this.IsMacPressingButtons())
				{
					this.sendStateToServer = true;
					this._trigger += ", OpponentStartedAttack";
				}
			}

			if (this.waitingForOpponentActionToEnd && !this.IsOpponentMovingInMemory())
			{
				this.waitingForOpponentActionToEnd = false;
			}
		}

		/// <summary>
		/// Verifies if Nac is idle
		/// </summary>
		private void IsMacIdle()
		{
		if (this.CanThrowPunches() == 1 &&	this.commandInQueueAvailable == false && !this.IsMacPressingButtons() && 
				this.IsRoundStarted() && !this.IsMacMovingOnMemory())
			{
				this.sendStateToServer = true;
				this._trigger += ", MacIsIdle";
			}
		}

		private void EnsureConnected()
		{
			if (_persistentClient == null || !_persistentClient.Connected)
			{
				// Clean up old connection if exists
				if (_persistentClient != null)
				{
					try { _persistentClient.Close(); } catch { }
				}
				
				_persistentClient = new TcpClient(PunchOutBot.serverAddress, PunchOutBot.clientPort);
				_persistentClient.NoDelay = true;
				_persistentStream = _persistentClient.GetStream();
			}
		}

		private void CloseConnection()
		{
			if (_persistentStream != null)
			{
				try { _persistentStream.Close(); } catch { }
				_persistentStream = null;
			}
			if (_persistentClient != null)
			{
				try { _persistentClient.Close(); } catch { }
				_persistentClient = null;
			}
		}

		private async Task<ControllerCommand> SendEmulatorGameStateToController(GameState state, int retry = 0, bool forceResume = false)
		{
			this.TakeScreenshot(state);
			ControllerCommand cc = new ControllerCommand();
			try
			{
				lock (_connectionLock)
				{
					EnsureConnected();
				}
				
				string data = JsonConvert.SerializeObject(state, _jsonSettings);
				byte[] msg = Encoding.UTF8.GetBytes(data);
				await _persistentStream.WriteAsync(msg, 0, msg.Length);

				if (!forceResume)
				{
					GlobalWin.MainForm.PauseEmulator();
				}
			}
			catch (ArgumentNullException ane)
			{
				cc.type = "__err__" + ane.ToString();
			}
			catch (SocketException se)
			{
				if (retry > 3)
				{
					throw se;
				}

				if (se.ErrorCode == 10061 || se.ErrorCode == 10053 || se.ErrorCode == 10054)
				{
					// Connection refused/reset - close and retry
					CloseConnection();
					Thread.Sleep(100);
					return await this.SendEmulatorGameStateToController(state, ++retry);
				}
				cc.type = "__err__" + se.ToString();
			}
			catch (IOException ioe)
			{
				// Connection lost - close and retry
				if (retry > 3)
				{
					throw ioe;
				}
				CloseConnection();
				Thread.Sleep(100);
				return await this.SendEmulatorGameStateToController(state, ++retry);
			}
			catch (Exception e)
			{
				cc.type = "__err__" + e.ToString();
			}
			return cc;
		}

		private void StartBot()
		{
			if (!CanStart())
			{
				MessageBox.Show("Unable to run with current settings");
				return;
			}

			_isBotting = true;
			RunBtn.Visible = false;
			StopBtn.Visible = true;
			CreateTcpServer(PunchOutBot.serverAddress, PunchOutBot.serverPort);

			Global.Config.SoundEnabled = false;
			GlobalWin.MainForm.UnpauseEmulator();
			SetMaxSpeed();
			if (Global.Config.emulator_speed_percent != 6399)
			{
				SetNormalSpeed();
			}
			GlobalWin.MainForm.ClickSpeedItem(Global.Config.emulator_speed_percent);

			UpdateBotStatusIcon();
			MessageLabel.Text = "Running...";
			_logGenerator = Global.MovieSession.LogGeneratorInstance();
			_logGenerator.SetSource(Global.ClickyVirtualPadController);
			_post_round_wait_time = Global.Config.round_over_delay;
			GlobalWin.OSD.AddMessageForTime("Game #: 0 Last Result: N/A P1 Wins-Losses: " + _wins + "-" + _losses + " (" + _winsToLosses + ") P2 Wins-Losses: " + _p2_wins + "-" + _p2_losses + "(" + _p2_winsToLosses + ")", _OSDMessageTimeInSeconds);

		}

		private bool CanStart()
		{


			return true;
		}

		private void StopBot()
		{
			this.server.Stop();
			CloseConnection(); // Close persistent connection to Python server
			RunBtn.Visible = true;
			StopBtn.Visible = false;
			_isBotting = false;



			GlobalWin.MainForm.PauseEmulator();
			SetNormalSpeed();
			UpdateBotStatusIcon();
			MessageLabel.Text = "Bot stopped";
		}

		private void UpdateBotStatusIcon()
		{
			if (_replayMode)
			{
				BotStatusButton.Image = Properties.Resources.Play;
				BotStatusButton.ToolTipText = "Replaying best result";
			}
			else if (_isBotting)
			{
				BotStatusButton.Image = Properties.Resources.RecordHS;
				BotStatusButton.ToolTipText = "Botting in progress";
			}
			else
			{
				BotStatusButton.Image = Properties.Resources.Pause;
				BotStatusButton.ToolTipText = "Bot is currently not running";
			}
		}

		private void SetMaxSpeed()
		{
			GlobalWin.MainForm.Unthrottle();
		}

		private void SetNormalSpeed()
		{
			GlobalWin.MainForm.Throttle();
		}
	}

	// Taken from http://www.mikeadev.net/2012/07/multi-threaded-tcp-server-in-csharp/
	class TcpServer
	{
		private TcpListener _server;
		public string commandInQueue = null;
		public Boolean commandInQueueAvailable = false;

		public delegate void MessageReceivedHandler(string message);
		public event MessageReceivedHandler onMessageReceived;

		public delegate void NotifyDestroy(TcpServer server);
		public event NotifyDestroy onDestroy;

		public TcpServer(string address, int port)
		{
			_server = new TcpListener(IPAddress.Parse(address), port);
			_server.Start();
		}

		public void LoopClients()
		{
			while (true)
			{
				try
				{
					// wait for client connection
					TcpClient newClient = _server.AcceptTcpClient();
					newClient.NoDelay = true; // Disable Nagle's algorithm for lower latency
					newClient.ReceiveBufferSize = 4096;

					// client found.
					// create a thread to handle communication
					HandleClient(newClient);
				}
				catch (Exception e)
				{
					throw e;
				}
			}
		}

		public void HandleClient(object obj)
		{
			// retrieve client from parameter passed to thread
			TcpClient client = (TcpClient)obj;

			// sets two streams
			StreamReader sReader = new StreamReader(client.GetStream(), Encoding.UTF8);

			// you could use the NetworkStream to read and write, 
			// but there is no forcing flush, even when requested

			StringBuilder sData = new StringBuilder();

			do
			{
				// reads from stream
				sData.Append(sReader.ReadLine());
			}
			while (client.Available > 0);

			// shows content on the console.
			//Console.WriteLine("Client &gt; " + sData);
			this.onMessageReceived(sData.ToString());
		}

		public void Stop()
		{
			this._server.Stop();
		}
	}
}

