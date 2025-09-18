import express from 'express';
import crypto from 'crypto';
import bs58 from 'bs58';
import {
  Connection,
  Keypair,
  VersionedTransaction,
  SystemProgram,
  PublicKey,
  LAMPORTS_PER_SOL,
  TransactionMessage,
} from '@solana/web3.js';

// -------------------- Config & Constants --------------------
const PORT = process.env.PORT || 3000;
const NETWORK = process.env.NETWORK || 'mainnet-beta';
const RPC_URL = process.env.RPC_URL || '';
const HMAC_SECRET = process.env.HMAC_SECRET || '';
const JUP_BASE = process.env.JUPITER_BASE || 'https://quote-api.jup.ag';
const PRIORITY_FEE = process.env.PRIORITIZATION_FEE_LAMPORTS ? Number(process.env.PRIORITIZATION_FEE_LAMPORTS) : undefined;

const DAILY_SOL_CAP_SOL = Number(process.env.DAILY_SOL_CAP_SOL || '5');
const PER_TOKEN_SOL_CAP_SOL = Number(process.env.PER_TOKEN_SOL_CAP_SOL || '0.5');
const PER_WALLET_SOL_CAP_SOL = Number(process.env.PER_WALLET_SOL_CAP_SOL || '1');
const COOLDOWN_MIN = Number(process.env.COOLDOWN_MIN || '60');

const WALLET_SELECTION = (process.env.WALLET_SELECTION || 'round_robin').toLowerCase();
const WALLET_WEIGHTS = (process.env.WALLET_WEIGHTS || '').split(',').map(s => Number(s.trim())).filter(n => Number.isFinite(n) && n > 0);

const TREASURY_INDEX = Number(process.env.TREASURY_INDEX || '0');
const TRANSFER_WHITELIST = (process.env.TRANSFER_WHITELIST || '')
  .split(',')
  .map(s => s.trim())
  .filter(Boolean);

const INPUT_MINT_WS0L = 'So11111111111111111111111111111111111111112';
const SLIPPAGE_BPS = 50;
const TIME_SKEW_SEC = 300;

// -------------------- Helpers --------------------
function todayKey() {
  const d = new Date();
  return d.toISOString().slice(0, 10); // YYYY-MM-DD
}

function timingSafeHexEqual(aHex, bHex) {
  const a = Buffer.from(aHex || '', 'hex');
  const b = Buffer.from(bHex || '', 'hex');
  if (a.length !== b.length) return false;
  return crypto.timingSafeEqual(a, b);
}

function signHmacHex(secret, raw, ts) {
  return crypto.createHmac('sha256', secret).update(raw + ts).digest('hex');
}

function jsonMinify(obj) {
  return JSON.stringify(obj);
}

function parseWalletsFromEnv() {
  const out = [];
  if (process.env.TRADER_SECRET_JSON) {
    try {
      const arr = JSON.parse(process.env.TRADER_SECRET_JSON);
      for (const entry of arr) {
        let kp;
        if (Array.isArray(entry)) {
          kp = Keypair.fromSecretKey(Uint8Array.from(entry));
        } else if (typeof entry === 'string') {
          kp = Keypair.fromSecretKey(bs58.decode(entry));
        } else if (entry && Array.isArray(entry.secretKey)) {
          kp = Keypair.fromSecretKey(Uint8Array.from(entry.secretKey));
        } else {
          continue;
        }
        out.push(kp);
      }
    } catch (e) {
      console.error('Failed parsing TRADER_SECRET_JSON:', e.message);
    }
  }
  if (process.env.TRADER_SECRET_BASE58) {
    const arr = process.env.TRADER_SECRET_BASE58.split(',').map(s => s.trim()).filter(Boolean);
    for (const b58 of arr) {
      try { out.push(Keypair.fromSecretKey(bs58.decode(b58))); } catch {}
    }
  }
  return out;
}

function pickIndexByWeights(weights) {
  const sum = weights.reduce((a, b) => a + b, 0);
  let r = Math.random() * sum;
  for (let i = 0; i < weights.length; i++) {
    if (r < weights[i]) return i;
    r -= weights[i];
  }
  return 0;
}

function hashToIndex(str, mod) {
  const h = crypto.createHash('sha256').update(str).digest();
  // Use first 4 bytes
  const n = h.readUInt32BE(0);
  return n % mod;
}

// -------------------- State --------------------
const app = express();
app.set('trust proxy', true);

// capture raw JSON
app.use(express.json({
  verify: (req, _res, buf) => { req.rawBody = buf.toString('utf8'); }
}));

if (!RPC_URL) {
  console.error('Missing RPC_URL');
  process.exit(1);
}
if (!HMAC_SECRET) {
  console.error('Missing HMAC_SECRET');
  process.exit(1);
}

const connection = new Connection(RPC_URL, 'confirmed');
const wallets = parseWalletsFromEnv();
if (wallets.length === 0) {
  console.error('No trader wallets loaded from env');
  process.exit(1);
}
if (WALLET_SELECTION === 'weighted' && WALLET_WEIGHTS.length !== wallets.length) {
  console.warn('WALLET_WEIGHTS length mismatch, falling back to round_robin');
}

let rrIndex = 0;
const limitsState = {
  dayKey: todayKey(),
  dailySpentLamports: 0,
  perTokenSpent: new Map(),   // mint -> lamports
  lastTradeAt: new Map(),     // mint -> unix sec
};

// -------------------- Middlewares --------------------
function requireHmac(req, res, next) {
  try {
    const ts = Number(req.get('X-Timestamp'));
    const sign = (req.get('X-Sign') || '').toLowerCase();
    if (!Number.isFinite(ts)) return res.status(401).json({ error: 'bad_hmac', message: 'missing timestamp' });
    const now = Math.floor(Date.now() / 1000);
    if (Math.abs(now - ts) > TIME_SKEW_SEC) return res.status(401).json({ error: 'bad_hmac', message: 'timestamp skew' });
    const raw = req.rawBody || '';
    const expected = signHmacHex(HMAC_SECRET, raw, String(ts));
    if (!timingSafeHexEqual(expected, sign)) return res.status(401).json({ error: 'bad_hmac', message: 'signature mismatch' });
    next();
  } catch (e) {
    return res.status(401).json({ error: 'bad_hmac', message: 'auth failed' });
  }
}

// -------------------- Risk & Selection --------------------
function refreshDayIfNeeded() {
  const k = todayKey();
  if (k !== limitsState.dayKey) {
    limitsState.dayKey = k;
    limitsState.dailySpentLamports = 0;
    limitsState.perTokenSpent.clear();
    // keep cooldowns
  }
}

function chooseWallet(mintOut) {
  if (wallets.length === 1) return { idx: 0, keypair: wallets[0] };
  if (WALLET_SELECTION === 'weighted' && WALLET_WEIGHTS.length === wallets.length) {
    const idx = pickIndexByWeights(WALLET_WEIGHTS);
    return { idx, keypair: wallets[idx] };
  }
  if (WALLET_SELECTION === 'by_token') {
    const idx = hashToIndex(mintOut, wallets.length);
    return { idx, keypair: wallets[idx] };
  }
  // round_robin
  const idx = rrIndex++ % wallets.length;
  return { idx, keypair: wallets[idx] };
}

function canProceedTrade(minLamportsAsk, mintOut) {
  refreshDayIfNeeded();
  const dailyCapLamports = DAILY_SOL_CAP_SOL * LAMPORTS_PER_SOL;
  const tokenCapLamports = PER_TOKEN_SOL_CAP_SOL * LAMPORTS_PER_SOL;

  if (limitsState.dailySpentLamports + minLamportsAsk > dailyCapLamports) {
    return { ok: false, reason: 'daily_cap' };
  }
  const prevToken = limitsState.perTokenSpent.get(mintOut) || 0;
  if (prevToken + minLamportsAsk > tokenCapLamports) {
    return { ok: false, reason: 'per_token_cap' };
  }
  const lastAt = limitsState.lastTradeAt.get(mintOut) || 0;
  const now = Math.floor(Date.now() / 1000);
  if (now - lastAt < (COOLDOWN_MIN * 60)) {
    return { ok: false, reason: 'cooldown' };
  }
  return { ok: true };
}

function recordTrade(mintOut, lamports) {
  refreshDayIfNeeded();
  limitsState.dailySpentLamports += lamports;
  limitsState.perTokenSpent.set(mintOut, (limitsState.perTokenSpent.get(mintOut) || 0) + lamports);
  limitsState.lastTradeAt.set(mintOut, Math.floor(Date.now() / 1000));
}

// -------------------- Jupiter --------------------
async function getQuoteLamports(mintOut, inLamports) {
  const url = new URL(`${JUP_BASE}/v6/quote`);
  url.searchParams.set('inputMint', INPUT_MINT_WS0L);
  url.searchParams.set('outputMint', mintOut);
  url.searchParams.set('amount', String(inLamports));
  url.searchParams.set('slippageBps', String(SLIPPAGE_BPS));
  url.searchParams.set('onlyDirectRoutes', 'false');
  url.searchParams.set('asLegacyTransaction', 'false');
  url.searchParams.set('platformFeeBps', '0');
  url.searchParams.set('maxAccounts', '32');
  url.searchParams.set('wrapAndUnwrapSol', 'true');

  const r = await fetch(url.toString(), { method: 'GET' });
  if (!r.ok) {
    throw new Error(`quote_http_${r.status}`);
  }
  const data = await r.json();
  if (!data || !data.inAmount || !data.outAmount) {
    throw new Error('quote_invalid');
  }
  return data; // quoteResponse to feed into /swap
}

async function buildSwapTxBase64(quoteResponse, userPublicKey) {
  const body = {
    quoteResponse,
    userPublicKey,
    wrapAndUnwrapSol: true,
    dynamicComputeUnitLimit: true,
    prioritizationFeeLamports: PRIORITY_FEE
  };
  const r = await fetch(`${JUP_BASE}/v6/swap`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: jsonMinify(body),
  });
  if (!r.ok) {
    const t = await r.text().catch(() => '');
    throw new Error(`swap_http_${r.status}:${t.slice(0,200)}`);
  }
  const data = await r.json();
  if (!data.swapTransaction) {
    throw new Error('swap_missing_tx');
  }
  return data.swapTransaction;
}

async function sendSignedTx(base64Tx, keypair) {
  const buf = Buffer.from(base64Tx, 'base64');
  const tx = VersionedTransaction.deserialize(buf);
  tx.sign([keypair]);
  const sig = await connection.sendRawTransaction(tx.serialize(), { skipPreflight: false, preflightCommitment: 'confirmed' });
  // confirm
  await connection.confirmTransaction(sig, 'confirmed');
  return sig;
}

// -------------------- Routes --------------------
app.get('/health', (_req, res) => {
  res.json({ ok: true, network: NETWORK, wallets: wallets.length });
});

app.get('/wallets', async (_req, res) => {
  try {
    const list = await Promise.all(wallets.map(async (kp, idx) => {
      const pub = kp.publicKey.toBase58();
      const bal = await connection.getBalance(kp.publicKey, { commitment: 'processed' }).catch(() => 0);
      return {
        index: idx,
        pubkey: pub,
        preview: `${pub.slice(0,4)}...${pub.slice(-4)}`,
        balanceSol: bal / LAMPORTS_PER_SOL,
        isTreasury: idx === TREASURY_INDEX
      };
    }));
    res.json({ ok: true, wallets: list });
  } catch (e) {
    res.status(500).json({ error: 'wallets_error', message: String(e.message || e) });
  }
});

app.post('/trade', requireHmac, async (req, res) => {
  try {
    const { mintOut, amountSol, source, meta } = req.body || {};
    if (typeof mintOut !== 'string' || !mintOut) return res.status(400).json({ error: 'bad_request', message: 'mintOut required' });
    if (!Number.isFinite(amountSol) || amountSol <= 0) return res.status(400).json({ error: 'bad_request', message: 'amountSol invalid' });

    // risk pre-check
    const lamportsAsk = Math.floor(amountSol * LAMPORTS_PER_SOL);
    const gate = canProceedTrade(lamportsAsk, mintOut);
    if (!gate.ok) {
      return res.status(429).json({ error: 'limits_blocked', reason: gate.reason });
    }

    // per-wallet cap check
    const pick = chooseWallet(mintOut);
    const walletBal = await connection.getBalance(wallets[pick.idx].publicKey).catch(() => 0);
    const perWalletCapLamports = PER_WALLET_SOL_CAP_SOL * LAMPORTS_PER_SOL;
    const maxSpendThisWallet = Math.max(0, Math.min(walletBal - 100000, perWalletCapLamports)); // keep 0.0001 SOL for rent
    if (lamportsAsk > maxSpendThisWallet) {
      return res.status(400).json({ error: 'per_wallet_cap', message: 'exceeds wallet cap/balance' });
    }

    // quote + swap
    const quote = await getQuoteLamports(mintOut, lamportsAsk);
    const swapBase64 = await buildSwapTxBase64(quote, wallets[pick.idx].publicKey.toBase58());
    const signature = await sendSignedTx(swapBase64, wallets[pick.idx]);

    // record & respond
    recordTrade(mintOut, lamportsAsk);
    res.json({
      ok: true,
      signature,
      walletIndex: pick.idx,
      wallet: wallets[pick.idx].publicKey.toBase58(),
      mintOut,
      inAmountLamports: Number(quote.inAmount),
      outAmount: quote.outAmount,
      routePlan: quote.routePlan?.length || 0,
      source: source || 'n8n'
    });
  } catch (e) {
    const msg = String(e.message || e);
    if (msg.startsWith('quote_')) return res.status(502).json({ error: 'quote_fail', message: msg });
    if (msg.startsWith('swap_')) return res.status(502).json({ error: 'swap_fail', message: msg });
    return res.status(500).json({ error: 'trade_error', message: msg });
  }
});

app.post('/transfer', requireHmac, async (req, res) => {
  try {
    const { fromIndex, to, amountSol } = req.body || {};
    if (!Number.isInteger(fromIndex) || fromIndex < 0 || fromIndex >= wallets.length) {
      return res.status(400).json({ error: 'bad_request', message: 'fromIndex invalid' });
    }
    if (!Number.isFinite(amountSol) || amountSol <= 0) {
      return res.status(400).json({ error: 'bad_request', message: 'amountSol invalid' });
    }
    let dest;
    // internal by index
    if (typeof to === 'number' && to >= 0 && to < wallets.length) {
      dest = wallets[to].publicKey;
    } else if (typeof to === 'string' && to.length > 0) {
      // external
      if (!TRANSFER_WHITELIST.includes(to)) return res.status(403).json({ error: 'forbidden', message: 'dest not whitelisted' });
      dest = new PublicKey(to);
    } else {
      return res.status(400).json({ error: 'bad_request', message: 'to invalid' });
    }

    const from = wallets[fromIndex];
    const lamports = Math.floor(amountSol * LAMPORTS_PER_SOL);
    const tx = new TransactionMessage({
      payerKey: from.publicKey,
      recentBlockhash: (await connection.getLatestBlockhash('finalized')).blockhash,
      instructions: [
        SystemProgram.transfer({ fromPubkey: from.publicKey, toPubkey: dest, lamports })
      ],
    }).compileToV0Message();
    const vtx = new VersionedTransaction(tx);
    vtx.sign([from]);
    const sig = await connection.sendRawTransaction(vtx.serialize(), { skipPreflight: false });
    await connection.confirmTransaction(sig, 'confirmed');
    res.json({ ok: true, signature: sig, from: from.publicKey.toBase58(), to: dest.toBase58(), amountSol });
  } catch (e) {
    res.status(500).json({ error: 'transfer_error', message: String(e.message || e) });
  }
});

app.post('/fund', requireHmac, async (req, res) => {
  try {
    const { mode, amountSol, minKeepSol } = req.body || {};
    const treasury = wallets[TREASURY_INDEX];
    if (!treasury) return res.status(400).json({ error: 'bad_request', message: 'treasury wallet missing' });

    const ops = [];
    if (mode === 'distribute') {
      // distribute equal parts from treasury to others up to per-wallet caps
      const amountPer = Number.isFinite(amountSol) ? amountSol : 0;
      for (let i = 0; i < wallets.length; i++) {
        if (i === TREASURY_INDEX) continue;
        const dest = wallets[i].publicKey;
        if (amountPer > 0) {
          ops.push({ from: treasury, to: dest, sol: amountPer });
        }
      }
    } else if (mode === 'collect') {
      // collect surplus from all wallets to treasury (keep at least minKeepSol in each)
      const keep = Number.isFinite(minKeepSol) ? minKeepSol : 0.05;
      for (let i = 0; i < wallets.length; i++) {
        if (i === TREASURY_INDEX) continue;
        const from = wallets[i];
        const bal = await connection.getBalance(from.publicKey);
        const spare = (bal / LAMPORTS_PER_SOL) - keep;
        if (spare > 0.001) {
          ops.push({ from, to: treasury.publicKey, sol: Math.max(0, spare - 0.0001) });
        }
      }
    } else {
      return res.status(400).json({ error: 'bad_request', message: 'mode must be distribute|collect' });
    }

    const results = [];
    for (const op of ops) {
      const lamports = Math.floor(op.sol * LAMPORTS_PER_SOL);
      if (lamports <= 0) continue;
      const tx = new TransactionMessage({
        payerKey: op.from.publicKey,
        recentBlockhash: (await connection.getLatestBlockhash('finalized')).blockhash,
        instructions: [
          SystemProgram.transfer({ fromPubkey: op.from.publicKey, toPubkey: op.to, lamports })
        ],
      }).compileToV0Message();
      const vtx = new VersionedTransaction(tx);
      vtx.sign([op.from]);
      const sig = await connection.sendRawTransaction(vtx.serialize(), { skipPreflight: false });
      await connection.confirmTransaction(sig, 'confirmed');
      results.push({ signature: sig, from: op.from.publicKey.toBase58(), to: op.to.toBase58(), amountSol: op.sol });
    }
    res.json({ ok: true, count: results.length, results });
  } catch (e) {
    res.status(500).json({ error: 'fund_error', message: String(e.message || e) });
  }
});

app.listen(PORT, () => {
  console.log(`Signer listening on :${PORT} (${NETWORK}), wallets=${wallets.length}`);
});
