import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode metadata: immediate bytes, values consumed, values produced.
const ops = [
  [0x00,0,0,0], [0x01,1,0,1], [0x02,4,0,1], [0x03,0,1,0],
  [0x04,0,1,2], [0x05,0,2,2], [0x06,0,2,3], [0x07,0,3,3],
  [0x10,0,2,1], [0x11,0,2,1], [0x12,0,2,1], [0x13,0,2,1],
  [0x14,0,2,1], [0x15,0,2,1], [0x16,0,2,1], [0x17,0,1,1],
  [0x18,0,2,1], [0x19,0,2,1], [0x1a,0,2,1], [0x1b,0,1,1],
  [0x1c,0,2,1], [0x1d,0,2,1], [0x1e,0,2,1],
  [0x20,0,2,1], [0x21,0,2,1], [0x22,0,2,1],
  [0x30,2,0,0], [0x31,2,1,0], [0x32,2,1,0],
  [0x33,2,0,0], [0x34,0,0,0], [0x40,0,1,1], [0x41,0,2,0],
  [0x50,0,1,0], [0x51,0,1,0], [0x52,0,0,1], [0x53,0,1,0],
];
const sizes = new Int8Array(256).fill(-1);
const pops = new Uint8Array(256), growth = new Int8Array(256);
for (const [op, imm, pop, push] of ops) {
  sizes[op] = imm; pops[op] = pop; growth[op] = push - pop;
}

function run(p, input) {
  const n = p.length;
  const code = new Uint8Array(n), operand = new Int32Array(n);
  const next = new Int32Array(n);
  // Decode every byte, including potential jump targets inside immediates.
  // Sentinels preserve unknown-opcode versus truncated-immediate precedence.
  for (let pc = 0; pc < n; pc++) {
    const op = p[pc], size = sizes[op];
    if (size < 0) { code[pc] = 255; continue; }
    if (pc + size >= n) { code[pc] = 254; continue; }
    code[pc] = op;
    next[pc] = pc + 1 + size;
    if (size === 1) operand[pc] = (p[pc + 1] << 24) >> 24;
    else if (size === 4) operand[pc] = p[pc + 1] | (p[pc + 2] << 8)
      | (p[pc + 3] << 16) | (p[pc + 4] << 24);
    else if (size === 2) {
      const v = p[pc + 1] | (p[pc + 2] << 8);
      operand[pc] = op === 0x33 ? v : next[pc] + ((v << 16) >> 16);
    }
  }
  const D = new Int32Array(256), C = new Int32Array(64);
  const M = new Int32Array(256), out = new Uint8Array(65536);
  const digits = new Uint8Array(10);
  let pc = 0, sp = 0, csp = 0, ip = 0, olen = 0, steps = 0;
  let exit = 10;
  execution: while (steps < 1000000) {
    if (pc < 0 || pc >= n) { exit = 9; break; }
    const op = code[pc];
    if (op === 255) { exit = 5; break; }
    if (op === 254) { exit = 9; break; }
    steps++;
    if (sp < pops[op]) { exit = 2; break; }
    if (sp + growth[op] > 256) { exit = 3; break; }
    const arg = operand[pc];
    pc = next[pc];
    switch (op) {
      case 0x00: exit = 0; break execution;
      case 0x01: case 0x02: D[sp++] = arg; break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: {
        const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t;
        break;
      }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: {
        const t = D[sp - 3]; D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1]; D[sp - 1] = t; break;
      }
      case 0x17: D[sp - 1] = (-D[sp - 1]) | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14:
      case 0x15: case 0x16: case 0x18: case 0x19: case 0x1a:
      case 0x1c: case 0x1d: case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r = 0;
        if (op >= 0x13 && op <= 0x16 && b === 0) {
          exit = 4; break execution;
        }
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13: r = (a / b) | 0; break;
          case 0x14: r = b === -1 ? 0 : (a % b) | 0; break;
          case 0x15: r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16: r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          case 0x22: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        D[--sp - 1] = r; break;
      }
      case 0x30: pc = arg; break;
      case 0x31: if (D[--sp] === 0) pc = arg; break;
      case 0x32: if (D[--sp] !== 0) pc = arg; break;
      case 0x33:
        if (csp === 64) { exit = 7; break execution; }
        C[csp++] = pc; pc = arg; break;
      case 0x34:
        if (csp === 0) { exit = 8; break execution; }
        pc = C[--csp]; break;
      case 0x40: case 0x41: {
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) { exit = 6; break execution; }
        if (op === 0x40) D[sp - 1] = M[addr];
        else { M[addr] = D[sp - 2]; sp -= 2; }
        break;
      }
      case 0x50: {
        const v = D[sp - 1];
        let x = v < 0 ? -v : v, count = 0;
        do {
          const q = Math.floor(x / 10);
          digits[count++] = 48 + x - q * 10; x = q;
        } while (x !== 0);
        if (olen + count + (v < 0 ? 1 : 0) > 65536) {
          exit = 11; break execution;
        }
        sp--;
        if (v < 0) out[olen++] = 45;
        while (count > 0) out[olen++] = digits[--count];
        break;
      }
      case 0x51:
        if (olen === 65536) { exit = 11; break execution; }
        out[olen++] = D[--sp] & 255; break;
      case 0x52: D[sp++] = ip < input.length ? input[ip++] : -1; break;
      case 0x53: exit = D[--sp] & 255; break execution;
    }
  }
  return { out: out.subarray(0, olen), code: exit };
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')),
    readFileSync(join(I, id, 'input.bin')));
  const dir = join(O, id);
  mkdirSync(dir, { recursive: true });
  writeFileSync(join(dir, 'stdout.bin'), r.out);
  writeFileSync(join(dir, 'exit.txt'), `${r.code}\n`);
}
