// Tiny stack VM: a faithful interpreter of make.fun's tiny stack ISA v1.
// One run answers every instance in MAKEFUN_INPUT_DIR, writing each
// instance's stdout.bin and exit.txt under MAKEFUN_OUTPUT_DIR.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

function run(p: Uint8Array, inp: Uint8Array): [Uint8Array, number] {
  const n = p.length;
  const D = new Int32Array(256); // data stack
  const C = new Int32Array(64); // call stack
  const M = new Int32Array(256); // memory words
  const o = new Uint8Array(65536); // output buffer
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, st = 0;
  const done = (c: number): [Uint8Array, number] => [o.slice(0, ol), c];
  for (;;) {
    if (st === 1000000) return done(10); // step limit
    if (pc < 0 || pc >= n) return done(9); // pc outside program
    const op = p[pc];
    const known = op < 0x08 || (op >= 0x10 && op <= 0x22) || (op >= 0x30 && op <= 0x34) || (op >= 0x40 && op <= 0x41) || (op >= 0x50 && op <= 0x53);
    if (!known) return done(5); // unknown opcode
    const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    if (pc + imm >= n) return done(9); // immediate cut off
    // Stack needs of this opcode: what it pops and what it pushes.
    const bin = op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b; // two-operand op
    const pops = op === 7 ? 3 : op === 5 || op === 6 || op === 0x41 || bin ? 2 : op === 3 || op === 4 || op === 0x17 || op === 0x1b || op === 0x31 || op === 0x32 || op === 0x40 || (op >= 0x50 && op !== 0x52) ? 1 : 0;
    const push = op === 6 || op === 7 ? 3 : op === 4 || op === 5 ? 2 : op === 1 || op === 2 || op === 0x40 || op === 0x52 || (op >= 0x10 && op <= 0x22) ? 1 : 0;
    st++;
    const nx = pc + 1 + imm;
    if (sp < pops) return done(2); // underflow
    if (sp - pops + push > 256) return done(3); // overflow
    pc = nx;
    // Two-operand arithmetic / logic / comparison (0x10-0x22 except NEG, NOT).
    if (bin) {
      const b = D[sp - 1], a = D[sp - 2];
      let r: number;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) {
        if (b === 0) return done(4);
        r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
      } else if (op === 0x14) {
        if (b === 0) return done(4);
        r = b === -1 ? 0 : (a % b) | 0;
      } else if (op === 0x15) {
        if (b === 0) return done(4);
        r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
      } else if (op === 0x16) {
        if (b === 0) return done(4);
        r = ((a >>> 0) % (b >>> 0)) | 0;
      } else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      sp -= 2;
      D[sp++] = r;
      continue;
    }
    switch (op) {
      case 0x00:
        return done(0); // HALT
      case 0x01:
        D[sp++] = (p[nx - 1] << 24) >> 24; // PUSH8, sign-extended
        break;
      case 0x02:
        D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); // PUSH32
        break;
      case 0x03:
        sp--; // POP
        break;
      case 0x04:
        D[sp] = D[sp - 1];
        sp++; // DUP
        break;
      case 0x05: {
        const t = D[sp - 1]; // SWAP
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 0x06:
        D[sp] = D[sp - 2];
        sp++; // OVER
        break;
      case 0x07: {
        const t = D[sp - 3]; // ROT
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = t;
        break;
      }
      case 0x17:
        D[sp - 1] = (-D[sp - 1]) | 0; // NEG
        break;
      case 0x1b:
        D[sp - 1] = ~D[sp - 1]; // NOT
        break;
      case 0x30:
      case 0x31:
      case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel; // JMP / JZ / JNZ
        break;
      }
      case 0x33:
        if (cp === 64) return done(7); // call depth
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8); // CALL
        break;
      case 0x34:
        if (cp === 0) return done(8); // RET on empty call stack
        pc = C[--cp];
        break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return done(6);
        D[sp - 1] = M[addr]; // LOAD
        break;
      }
      case 0x41: {
        const addr = D[sp - 1], v = D[sp - 2];
        if (addr < 0 || addr >= 256) return done(6);
        sp -= 2;
        M[addr] = v; // STORE
        break;
      }
      case 0x50: {
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return done(11); // output limit
        sp--;
        for (let i = 0; i < s.length; i++) o[ol++] = s.charCodeAt(i); // PRINT
        break;
      }
      case 0x51:
        if (ol + 1 > 65536) return done(11);
        o[ol++] = D[--sp] & 255; // PUTC
        break;
      case 0x52:
        D[sp++] = ip < inp.length ? inp[ip++] : -1; // IN
        break;
      case 0x53:
        return done(D[--sp] & 255); // EXIT
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const O = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";
for (const id of readdirSync(I).sort()) {
  const [out, code] = run(
    new Uint8Array(readFileSync(join(I, id, "program.bin"))),
    new Uint8Array(readFileSync(join(I, id, "input.bin"))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, "stdout.bin"), out);
  writeFileSync(join(O, id, "exit.txt"), code + "\n");
}
