/**
 * x86 8086 CPU Core - Complete TypeScript Implementation
 *
 * 完全命令セット:
 *   - 全汎用命令 (MOV/ADD/SUB/MUL/DIV/...)
 *   - 文字列命令 + REP/REPNE プレフィックス
 *   - シフト・ローテート命令
 *   - BCD演算命令
 *   - セグメントオーバーライドプレフィックス
 *   - 割り込みシステム (INT/IRET)
 *   - I/Oポートシステム
 *   - 0Fプレフィックス命令
 */
// ============================================================
// フラグビット定義
// ============================================================
const FLAGS = {
    CF: 1 << 0, // Carry Flag
    PF: 1 << 2, // Parity Flag
    AF: 1 << 4, // Auxiliary Carry Flag
    ZF: 1 << 6, // Zero Flag
    SF: 1 << 7, // Sign Flag
    TF: 1 << 8, // Trap Flag
    IF: 1 << 9, // Interrupt Enable Flag
    DF: 1 << 10, // Direction Flag
    OF: 1 << 11, // Overflow Flag
};
// ============================================================
// メモリ (1MB = 0x00000 〜 0xFFFFF)
// ============================================================
class Memory {
    constructor(size = 0x100000) {
        this.data = new Uint8Array(size);
    }
    read8(addr) {
        return this.data[addr & 0xFFFFF];
    }
    write8(addr, val) {
        this.data[addr & 0xFFFFF] = val & 0xFF;
    }
    read16(addr) {
        return this.read8(addr) | (this.read8(addr + 1) << 8);
    }
    write16(addr, val) {
        this.write8(addr, val & 0xFF);
        this.write8(addr + 1, (val >> 8) & 0xFF);
    }
    load(addr, data) {
        for (let i = 0; i < data.length; i++) {
            this.write8(addr + i, data[i]);
        }
    }
}
// ============================================================
// レジスタ
// ============================================================
class Registers {
    constructor() {
        this.ax = 0;
        this.bx = 0;
        this.cx = 0;
        this.dx = 0;
        this.si = 0;
        this.di = 0;
        this.bp = 0;
        this.sp = 0xFFFE;
        this.cs = 0xF000;
        this.ds = 0;
        this.es = 0;
        this.ss = 0;
        this.fs = 0;
        this.gs = 0;
        this.ip = 0xFFF0;
        this.flags = 0x0002;
    }
    // 8bit アクセサ
    get al() { return this.ax & 0xFF; }
    get ah() { return (this.ax >> 8) & 0xFF; }
    get bl() { return this.bx & 0xFF; }
    get bh() { return (this.bx >> 8) & 0xFF; }
    get cl() { return this.cx & 0xFF; }
    get ch() { return (this.cx >> 8) & 0xFF; }
    get dl() { return this.dx & 0xFF; }
    get dh() { return (this.dx >> 8) & 0xFF; }
    set al(v) { this.ax = (this.ax & 0xFF00) | (v & 0xFF); }
    set ah(v) { this.ax = (this.ax & 0x00FF) | ((v & 0xFF) << 8); }
    set bl(v) { this.bx = (this.bx & 0xFF00) | (v & 0xFF); }
    set bh(v) { this.bx = (this.bx & 0x00FF) | ((v & 0xFF) << 8); }
    set cl(v) { this.cx = (this.cx & 0xFF00) | (v & 0xFF); }
    set ch(v) { this.cx = (this.cx & 0x00FF) | ((v & 0xFF) << 8); }
    set dl(v) { this.dx = (this.dx & 0xFF00) | (v & 0xFF); }
    set dh(v) { this.dx = (this.dx & 0x00FF) | ((v & 0xFF) << 8); }
    getFlag(bit) { return (this.flags & bit) !== 0; }
    setFlag(bit, val) {
        if (val)
            this.flags |= bit;
        else
            this.flags &= ~bit;
    }
    segmented(seg, off) {
        return ((seg << 4) + (off & 0xFFFF)) & 0xFFFFF;
    }
}
// ============================================================
// ModRM デコード
// ============================================================
function decodeModRM(byte) {
    return {
        mod: (byte >> 6) & 0x3,
        reg: (byte >> 3) & 0x7,
        rm: byte & 0x7,
    };
}
// ============================================================
// CPU コア
// ============================================================
class CPU8086 {
    constructor(mem) {
        this.halted = false;
        this.haltReason = ''; // 'hlt', 'program_exit', 'key_wait', ''
        this.waitCycles = 0;
        // セグメントオーバーライド (null = デフォルト)
        this.segOverride = null;
        // REP/REPNE プレフィックス
        this.repPrefix = null;
        // 割り込みハンドラ
        this.interruptHandlers = new Map();
        // I/Oポートハンドラ
        this.ioPortHandlers = new Map();
        // デバッグ
        this.debugLog = [];
        this.debugMode = false;
        // 最後に計算したEAをキャッシュ (read-modify-writeパターン用)
        this._lastEA = 0;
        this._eaCached = false;
        this._lastStrOpSetsZF = false; // SCAS/CMPSのみZFチェック
        // ================================================================
        // BIOS初期化
        // ================================================================
        this.biosOutputBuffer = '';
        this.biosKeyBuffer = [];
        this.biosVideoMode = 0x03; // 80x25 color text
        this.biosCursorRow = 0;
        this.biosCursorCol = 0;
        this.biosVideoRows = 25;
        this.biosVideoCols = 80;
        this.biosCharHeight = 16;
        // VRAM: B800:0000 (80x25 text mode = 4000 bytes)
        this.VRAM_SEG = 0xB800;
        this.VRAM_BASE = 0xB8000;
        // DOS file I/O handler (set by msdos.js DOSFileIO)
        this.dosFileIO = null;
        // Mouse state
        this.mouseX = 0;
        this.mouseY = 0;
        this.mouseButtons = 0;
        // Timer
        this.timerCounter = 0;
        this.timerInterval = 0;
        this.reg = new Registers();
        this.mem = mem !== null && mem !== void 0 ? mem : new Memory();
    }
    // ============================================================
    // 外部API
    // ============================================================
    registerInterrupt(vector, handler) {
        this.interruptHandlers.set(vector, handler);
    }
    registerIOPort(port, read, write) {
        this.ioPortHandlers.set(port, { read, write });
    }
    reset() {
        this.reg = new Registers();
        this.halted = false;
        this.haltReason = '';
        this.waitCycles = 0;
        this.segOverride = null;
        this.repPrefix = null;
    }
    // ============================================================
    // フェッチ
    // ============================================================
    fetchByte() {
        const addr = this.reg.segmented(this.reg.cs, this.reg.ip);
        const val = this.mem.read8(addr);
        this.reg.ip = (this.reg.ip + 1) & 0xFFFF;
        return val;
    }
    fetchWord() {
        return this.fetchByte() | (this.fetchByte() << 8);
    }
    fetchSByte() {
        const v = this.fetchByte();
        return v >= 0x80 ? v - 0x100 : v;
    }
    fetchSWord() {
        const v = this.fetchWord();
        return v >= 0x8000 ? v - 0x10000 : v;
    }
    // ============================================================
    // スタック
    // ============================================================
    push(val) {
        this.reg.sp = (this.reg.sp - 2) & 0xFFFF;
        this.mem.write16(this.reg.segmented(this.reg.ss, this.reg.sp), val & 0xFFFF);
    }
    pop() {
        const val = this.mem.read16(this.reg.segmented(this.reg.ss, this.reg.sp));
        this.reg.sp = (this.reg.sp + 2) & 0xFFFF;
        return val;
    }
    // ============================================================
    // セグメント解決 (オーバーライド対応)
    // ============================================================
    resolveSeg(defaultSeg) {
        return this.segOverride !== null ? this.segOverride : defaultSeg;
    }
    segAddr(defaultSeg, off) {
        return this.reg.segmented(this.resolveSeg(defaultSeg), off);
    }
    // ============================================================
    // パリティ
    // ============================================================
    parity(val) {
        let p = 0;
        for (let v = val & 0xFF; v; v >>= 1)
            p ^= v & 1;
        return p === 0;
    }
    // ============================================================
    // フラグ更新
    // ============================================================
    updateZSP8(r) {
        const v = r & 0xFF;
        this.reg.setFlag(FLAGS.ZF, v === 0);
        this.reg.setFlag(FLAGS.SF, (v & 0x80) !== 0);
        this.reg.setFlag(FLAGS.PF, this.parity(v));
    }
    updateZSP16(r) {
        const v = r & 0xFFFF;
        this.reg.setFlag(FLAGS.ZF, v === 0);
        this.reg.setFlag(FLAGS.SF, (v & 0x8000) !== 0);
        this.reg.setFlag(FLAGS.PF, this.parity(v));
    }
    // ============================================================
    // 算術演算 (フラグ含む)
    // ============================================================
    add8(a, b, carry = 0) {
        a &= 0xFF;
        b &= 0xFF;
        const r = a + b + carry;
        this.reg.setFlag(FLAGS.CF, r > 0xFF);
        this.reg.setFlag(FLAGS.OF, ((~(a ^ b)) & (a ^ r) & 0x80) !== 0);
        this.reg.setFlag(FLAGS.AF, ((a ^ b ^ r) & 0x10) !== 0);
        this.updateZSP8(r);
        return r & 0xFF;
    }
    add16(a, b, carry = 0) {
        a &= 0xFFFF;
        b &= 0xFFFF;
        const r = a + b + carry;
        this.reg.setFlag(FLAGS.CF, r > 0xFFFF);
        this.reg.setFlag(FLAGS.OF, ((~(a ^ b)) & (a ^ r) & 0x8000) !== 0);
        this.reg.setFlag(FLAGS.AF, ((a ^ b ^ r) & 0x10) !== 0);
        this.updateZSP16(r);
        return r & 0xFFFF;
    }
    sub8(a, b, borrow = 0) {
        a &= 0xFF;
        b &= 0xFF;
        const r = a - b - borrow;
        this.reg.setFlag(FLAGS.CF, r < 0);
        this.reg.setFlag(FLAGS.OF, ((a ^ b) & (a ^ (r & 0xFF)) & 0x80) !== 0);
        this.reg.setFlag(FLAGS.AF, ((a ^ b ^ (r & 0xFF)) & 0x10) !== 0);
        this.updateZSP8(r);
        return r & 0xFF;
    }
    sub16(a, b, borrow = 0) {
        a &= 0xFFFF;
        b &= 0xFFFF;
        const r = a - b - borrow;
        this.reg.setFlag(FLAGS.CF, r < 0);
        this.reg.setFlag(FLAGS.OF, ((a ^ b) & (a ^ (r & 0xFFFF)) & 0x8000) !== 0);
        this.reg.setFlag(FLAGS.AF, ((a ^ b ^ (r & 0xFFFF)) & 0x10) !== 0);
        this.updateZSP16(r);
        return r & 0xFFFF;
    }
    // ============================================================
    // レジスタ番号アクセサ
    // ============================================================
    getReg8(r) {
        switch (r) {
            case 0: return this.reg.al;
            case 1: return this.reg.cl;
            case 2: return this.reg.dl;
            case 3: return this.reg.bl;
            case 4: return this.reg.ah;
            case 5: return this.reg.ch;
            case 6: return this.reg.dh;
            case 7: return this.reg.bh;
            default: return 0;
        }
    }
    setReg8(r, v) {
        v &= 0xFF;
        switch (r) {
            case 0:
                this.reg.al = v;
                break;
            case 1:
                this.reg.cl = v;
                break;
            case 2:
                this.reg.dl = v;
                break;
            case 3:
                this.reg.bl = v;
                break;
            case 4:
                this.reg.ah = v;
                break;
            case 5:
                this.reg.ch = v;
                break;
            case 6:
                this.reg.dh = v;
                break;
            case 7:
                this.reg.bh = v;
                break;
        }
    }
    getReg16(r) {
        switch (r) {
            case 0: return this.reg.ax;
            case 1: return this.reg.cx;
            case 2: return this.reg.dx;
            case 3: return this.reg.bx;
            case 4: return this.reg.sp;
            case 5: return this.reg.bp;
            case 6: return this.reg.si;
            case 7: return this.reg.di;
            default: return 0;
        }
    }
    setReg16(r, v) {
        v &= 0xFFFF;
        switch (r) {
            case 0:
                this.reg.ax = v;
                break;
            case 1:
                this.reg.cx = v;
                break;
            case 2:
                this.reg.dx = v;
                break;
            case 3:
                this.reg.bx = v;
                break;
            case 4:
                this.reg.sp = v;
                break;
            case 5:
                this.reg.bp = v;
                break;
            case 6:
                this.reg.si = v;
                break;
            case 7:
                this.reg.di = v;
                break;
        }
    }
    getSegReg(r) {
        switch (r) {
            case 0: return this.reg.es;
            case 1: return this.reg.cs;
            case 2: return this.reg.ss;
            case 3: return this.reg.ds;
            default: return 0;
        }
    }
    setSegReg(r, v) {
        switch (r) {
            case 0:
                this.reg.es = v;
                break;
            case 1:
                this.reg.cs = v;
                break;
            case 2:
                this.reg.ss = v;
                break;
            case 3:
                this.reg.ds = v;
                break;
        }
    }
    // ============================================================
    // ModRM: 実効アドレス計算
    // ============================================================
    calcEA(mod, rm) {
        let base = 0;
        let defaultSeg = this.reg.ds;
        switch (rm) {
            case 0:
                base = (this.reg.bx + this.reg.si) & 0xFFFF;
                break;
            case 1:
                base = (this.reg.bx + this.reg.di) & 0xFFFF;
                break;
            case 2:
                base = (this.reg.bp + this.reg.si) & 0xFFFF;
                defaultSeg = this.reg.ss;
                break;
            case 3:
                base = (this.reg.bp + this.reg.di) & 0xFFFF;
                defaultSeg = this.reg.ss;
                break;
            case 4:
                base = this.reg.si;
                break;
            case 5:
                base = this.reg.di;
                break;
            case 6:
                if (mod === 0) {
                    base = this.fetchWord();
                }
                else {
                    base = this.reg.bp;
                    defaultSeg = this.reg.ss;
                }
                break;
            case 7:
                base = this.reg.bx;
                break;
        }
        if (mod === 1)
            base = (base + this.fetchSByte()) & 0xFFFF;
        else if (mod === 2)
            base = (base + this.fetchSWord()) & 0xFFFF;
        this._lastEA = this.reg.segmented(this.resolveSeg(defaultSeg), base);
        this._eaCached = true;
        return this._lastEA;
    }
    // ModRM全解析 (EA or reg番号を返す)
    readRM8(mod, rm) {
        if (mod === 3)
            return this.getReg8(rm);
        return this.mem.read8(this.calcEA(mod, rm));
    }
    writeRM8(mod, rm, val) {
        if (mod === 3) {
            this.setReg8(rm, val);
            return;
        }
        // _eaCachedがtrueなら直前のreadRMで計算済みのEAを再利用
        // falseなら新規にcalcEAを呼ぶ
        const ea = this._eaCached ? this._lastEA : this.calcEA(mod, rm);
        this.mem.write8(ea, val);
    }
    readRM16(mod, rm) {
        if (mod === 3)
            return this.getReg16(rm);
        return this.mem.read16(this.calcEA(mod, rm));
    }
    writeRM16(mod, rm, val) {
        if (mod === 3) {
            this.setReg16(rm, val);
            return;
        }
        const ea = this._eaCached ? this._lastEA : this.calcEA(mod, rm);
        this.mem.write16(ea, val);
    }
    // ============================================================
    // シフト・ローテート (D0/D1/D2/D3/C0/C1グループ)
    // ============================================================
    doShift8(op, val, cnt) {
        let v = val & 0xFF;
        cnt &= 0x1F;
        if (cnt === 0)
            return v;
        let result = v;
        const cf = this.reg.getFlag(FLAGS.CF);
        switch (op) {
            case 0: // ROL
                for (let i = 0; i < cnt; i++) {
                    const msb = (result >> 7) & 1;
                    result = ((result << 1) | msb) & 0xFF;
                    this.reg.setFlag(FLAGS.CF, msb !== 0);
                }
                if (cnt === 1)
                    this.reg.setFlag(FLAGS.OF, ((result >> 7) & 1) !== (this.reg.getFlag(FLAGS.CF) ? 1 : 0));
                break;
            case 1: // ROR
                for (let i = 0; i < cnt; i++) {
                    const lsb = result & 1;
                    result = ((lsb << 7) | (result >> 1)) & 0xFF;
                    this.reg.setFlag(FLAGS.CF, lsb !== 0);
                }
                if (cnt === 1)
                    this.reg.setFlag(FLAGS.OF, ((result >> 7) ^ ((result >> 6) & 1)) !== 0);
                break;
            case 2: // RCL
                for (let i = 0; i < cnt; i++) {
                    const oldCF = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                    this.reg.setFlag(FLAGS.CF, (result & 0x80) !== 0);
                    result = ((result << 1) | oldCF) & 0xFF;
                }
                if (cnt === 1)
                    this.reg.setFlag(FLAGS.OF, ((result >> 7) & 1) !== (this.reg.getFlag(FLAGS.CF) ? 1 : 0));
                break;
            case 3: // RCR
                for (let i = 0; i < cnt; i++) {
                    const oldCF = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                    this.reg.setFlag(FLAGS.CF, (result & 1) !== 0);
                    result = ((oldCF << 7) | (result >> 1)) & 0xFF;
                }
                if (cnt === 1)
                    this.reg.setFlag(FLAGS.OF, ((result >> 7) ^ ((result >> 6) & 1)) !== 0);
                break;
            case 4:
            case 6: // SHL/SAL
                this.reg.setFlag(FLAGS.CF, cnt <= 8 ? ((v >> (8 - cnt)) & 1) !== 0 : false);
                result = (v << cnt) & 0xFF;
                this.updateZSP8(result);
                if (cnt === 1)
                    this.reg.setFlag(FLAGS.OF, ((result >> 7) & 1) !== (this.reg.getFlag(FLAGS.CF) ? 1 : 0));
                break;
            case 5: // SHR
                this.reg.setFlag(FLAGS.CF, cnt <= 8 ? ((v >> (cnt - 1)) & 1) !== 0 : false);
                result = (v >> cnt) & 0xFF;
                this.updateZSP8(result);
                if (cnt === 1)
                    this.reg.setFlag(FLAGS.OF, (v & 0x80) !== 0);
                break;
            case 7: // SAR
                this.reg.setFlag(FLAGS.CF, ((v >> (cnt - 1)) & 1) !== 0);
                const signBit = v & 0x80;
                result = v;
                for (let i = 0; i < cnt; i++)
                    result = ((result >> 1) | signBit) & 0xFF;
                this.updateZSP8(result);
                if (cnt === 1)
                    this.reg.setFlag(FLAGS.OF, false);
                break;
        }
        return result & 0xFF;
    }
    doShift16(op, val, cnt) {
        let v = val & 0xFFFF;
        cnt &= 0x1F;
        if (cnt === 0)
            return v;
        let result = v;
        switch (op) {
            case 0: // ROL
                for (let i = 0; i < cnt; i++) {
                    const msb = (result >> 15) & 1;
                    result = ((result << 1) | msb) & 0xFFFF;
                    this.reg.setFlag(FLAGS.CF, msb !== 0);
                }
                if (cnt === 1)
                    this.reg.setFlag(FLAGS.OF, ((result >> 15) & 1) !== (this.reg.getFlag(FLAGS.CF) ? 1 : 0));
                break;
            case 1: // ROR
                for (let i = 0; i < cnt; i++) {
                    const lsb = result & 1;
                    result = ((lsb << 15) | (result >> 1)) & 0xFFFF;
                    this.reg.setFlag(FLAGS.CF, lsb !== 0);
                }
                if (cnt === 1)
                    this.reg.setFlag(FLAGS.OF, ((result >> 15) ^ ((result >> 14) & 1)) !== 0);
                break;
            case 2: // RCL
                for (let i = 0; i < cnt; i++) {
                    const oldCF = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                    this.reg.setFlag(FLAGS.CF, (result & 0x8000) !== 0);
                    result = ((result << 1) | oldCF) & 0xFFFF;
                }
                if (cnt === 1)
                    this.reg.setFlag(FLAGS.OF, ((result >> 15) & 1) !== (this.reg.getFlag(FLAGS.CF) ? 1 : 0));
                break;
            case 3: // RCR
                for (let i = 0; i < cnt; i++) {
                    const oldCF = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                    this.reg.setFlag(FLAGS.CF, (result & 1) !== 0);
                    result = ((oldCF << 15) | (result >> 1)) & 0xFFFF;
                }
                if (cnt === 1)
                    this.reg.setFlag(FLAGS.OF, ((result >> 15) ^ ((result >> 14) & 1)) !== 0);
                break;
            case 4:
            case 6: // SHL/SAL
                this.reg.setFlag(FLAGS.CF, cnt <= 16 ? ((v >> (16 - cnt)) & 1) !== 0 : false);
                result = (v << cnt) & 0xFFFF;
                this.updateZSP16(result);
                if (cnt === 1)
                    this.reg.setFlag(FLAGS.OF, ((result >> 15) & 1) !== (this.reg.getFlag(FLAGS.CF) ? 1 : 0));
                break;
            case 5: // SHR
                this.reg.setFlag(FLAGS.CF, cnt <= 16 ? ((v >> (cnt - 1)) & 1) !== 0 : false);
                result = (v >> cnt) & 0xFFFF;
                this.updateZSP16(result);
                if (cnt === 1)
                    this.reg.setFlag(FLAGS.OF, (v & 0x8000) !== 0);
                break;
            case 7: // SAR
                this.reg.setFlag(FLAGS.CF, ((v >> (cnt - 1)) & 1) !== 0);
                const signBit = v & 0x8000;
                result = v;
                for (let i = 0; i < cnt; i++)
                    result = ((result >> 1) | signBit) & 0xFFFF;
                this.updateZSP16(result);
                if (cnt === 1)
                    this.reg.setFlag(FLAGS.OF, false);
                break;
        }
        return result & 0xFFFF;
    }
    // ============================================================
    // 割り込み処理
    // ============================================================
    doInterrupt(vector) {
        const handler = this.interruptHandlers.get(vector);
        if (handler) {
            handler();
            if (this.halted) {
                // handler内でhaltedにした場合（キー入力待ち等）
                // スタックからIP/CS/Flagsを復元するが、handlerがIPを巻き戻した場合はそちらを優先
                // スタックを掃除だけする
                this.pop(); // ip (捨てる - handlerが設定したIPを使う)
                this.pop(); // cs (捨てる)
                this.reg.flags = this.pop(); // flagsだけ復元
            }
            else {
                // 正常完了: スタック掃除して戻す
                this.reg.ip = this.pop();
                this.reg.cs = this.pop();
                this.reg.flags = this.pop();
            }
        }
        else {
            // 本物のIVTジャンプ（これは今のままでOK）
            const ip = this.mem.read16(vector * 4);
            const cs = this.mem.read16(vector * 4 + 2);
            this.reg.cs = cs;
            this.reg.ip = ip;
        }
    }
    // ============================================================
    // I/O
    // ============================================================
    ioRead(port) {
        const h = this.ioPortHandlers.get(port & 0xFFFF);
        return h ? h.read() : 0xFF;
    }
    ioWrite(port, val) {
        const h = this.ioPortHandlers.get(port & 0xFFFF);
        if (h)
            h.write(val & 0xFF);
    }
    // ============================================================
    // 文字列命令の1ステップ実行
    // ============================================================
    strStep(op) {
        const rep = this.repPrefix;
        if (rep === null) {
            op();
        }
        else {
            while (this.reg.cx !== 0) {
                op();
                this.reg.cx = (this.reg.cx - 1) & 0xFFFF;
                if (rep === 'REPNE' && this.reg.getFlag(FLAGS.ZF))
                    break;
                if (rep === 'REP' && !this.reg.getFlag(FLAGS.ZF) && (this._lastStrOpSetsZF))
                    break;
            }
        }
        this.repPrefix = null;
        this.segOverride = null;
    }
    siDir() { return this.reg.getFlag(FLAGS.DF) ? -1 : 1; }
    // ============================================================
    // メイン: 1命令実行
    // ============================================================
    step() {
        if (this.halted)
            return false;
        // INT 15h/86h ウェイト処理
        if (this.waitCycles > 0) {
            this.waitCycles--;
            return true;
        }
        // プレフィックスをクリア
        this.segOverride = null;
        this.repPrefix = null;
        this._step();
        return !this.halted;
    }
    _step() {
        const opcode = this.fetchByte();
        this._eaCached = false;
        if (this.debugMode) {
            this.debugLog.push(`[${this.reg.cs.toString(16).padStart(4, '0')}:${((this.reg.ip - 1) & 0xFFFF).toString(16).padStart(4, '0')}] ${opcode.toString(16).padStart(2, '0')}`);
        }
        switch (opcode) {
            // ================================================================
            // プレフィックス
            // ================================================================
            case 0x26:
                this.segOverride = this.reg.es;
                this._step();
                return; // ES:
            case 0x2E:
                this.segOverride = this.reg.cs;
                this._step();
                return; // CS:
            case 0x36:
                this.segOverride = this.reg.ss;
                this._step();
                return; // SS:
            case 0x3E:
                this.segOverride = this.reg.ds;
                this._step();
                return; // DS:
            case 0x64:
                this.segOverride = this.reg.fs;
                this._step();
                return; // FS:
            case 0x65:
                this.segOverride = this.reg.gs;
                this._step();
                return; // GS:
            case 0xF0:
                this._step();
                return; // LOCK (ignore)
            case 0xF2:
                this.repPrefix = 'REPNE';
                this._step();
                return; // REPNE/REPNZ
            case 0xF3:
                this.repPrefix = 'REP';
                this._step();
                return; // REP/REPE/REPZ
            // ================================================================
            // ADD  (00-05)
            // ================================================================
            case 0x00: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.writeRM8(mod, rm, this.add8(this.readRM8(mod, rm), this.getReg8(reg)));
                break;
            }
            case 0x01: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.writeRM16(mod, rm, this.add16(this.readRM16(mod, rm), this.getReg16(reg)));
                break;
            }
            case 0x02: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.setReg8(reg, this.add8(this.getReg8(reg), this.readRM8(mod, rm)));
                break;
            }
            case 0x03: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.setReg16(reg, this.add16(this.getReg16(reg), this.readRM16(mod, rm)));
                break;
            }
            case 0x04:
                this.reg.al = this.add8(this.reg.al, this.fetchByte());
                break;
            case 0x05:
                this.reg.ax = this.add16(this.reg.ax, this.fetchWord());
                break;
            // ================================================================
            // PUSH/POP ES (06/07)
            // ================================================================
            case 0x06:
                this.push(this.reg.es);
                break;
            case 0x07:
                this.reg.es = this.pop();
                break;
            // ================================================================
            // OR (08-0D)
            // ================================================================
            case 0x08: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const r = this.readRM8(mod, rm) | this.getReg8(reg);
                this.updateZSP8(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.writeRM8(mod, rm, r);
                break;
            }
            case 0x09: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const r = this.readRM16(mod, rm) | this.getReg16(reg);
                this.updateZSP16(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.writeRM16(mod, rm, r);
                break;
            }
            case 0x0A: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const r = this.getReg8(reg) | this.readRM8(mod, rm);
                this.updateZSP8(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.setReg8(reg, r);
                break;
            }
            case 0x0B: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const r = this.getReg16(reg) | this.readRM16(mod, rm);
                this.updateZSP16(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.setReg16(reg, r);
                break;
            }
            case 0x0C: {
                const r = this.reg.al | this.fetchByte();
                this.updateZSP8(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.reg.al = r;
                break;
            }
            case 0x0D: {
                const r = this.reg.ax | this.fetchWord();
                this.updateZSP16(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.reg.ax = r;
                break;
            }
            // ================================================================
            // PUSH/POP CS (0E) / 0F prefix
            // ================================================================
            case 0x0E:
                this.push(this.reg.cs);
                break;
            case 0x0F:
                this.exec0F();
                break;
            // ================================================================
            // ADC (10-15)
            // ================================================================
            case 0x10: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const cf = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                this.writeRM8(mod, rm, this.add8(this.readRM8(mod, rm), this.getReg8(reg), cf));
                break;
            }
            case 0x11: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const cf = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                this.writeRM16(mod, rm, this.add16(this.readRM16(mod, rm), this.getReg16(reg), cf));
                break;
            }
            case 0x12: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const cf = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                this.setReg8(reg, this.add8(this.getReg8(reg), this.readRM8(mod, rm), cf));
                break;
            }
            case 0x13: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const cf = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                this.setReg16(reg, this.add16(this.getReg16(reg), this.readRM16(mod, rm), cf));
                break;
            }
            case 0x14: {
                const cf = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                this.reg.al = this.add8(this.reg.al, this.fetchByte(), cf);
                break;
            }
            case 0x15: {
                const cf = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                this.reg.ax = this.add16(this.reg.ax, this.fetchWord(), cf);
                break;
            }
            // ================================================================
            // PUSH/POP SS (16/17)
            // ================================================================
            case 0x16:
                this.push(this.reg.ss);
                break;
            case 0x17:
                this.reg.ss = this.pop();
                break;
            // ================================================================
            // SBB (18-1D)
            // ================================================================
            case 0x18: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const cf = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                this.writeRM8(mod, rm, this.sub8(this.readRM8(mod, rm), this.getReg8(reg), cf));
                break;
            }
            case 0x19: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const cf = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                this.writeRM16(mod, rm, this.sub16(this.readRM16(mod, rm), this.getReg16(reg), cf));
                break;
            }
            case 0x1A: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const cf = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                this.setReg8(reg, this.sub8(this.getReg8(reg), this.readRM8(mod, rm), cf));
                break;
            }
            case 0x1B: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const cf = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                this.setReg16(reg, this.sub16(this.getReg16(reg), this.readRM16(mod, rm), cf));
                break;
            }
            case 0x1C: {
                const cf = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                this.reg.al = this.sub8(this.reg.al, this.fetchByte(), cf);
                break;
            }
            case 0x1D: {
                const cf = this.reg.getFlag(FLAGS.CF) ? 1 : 0;
                this.reg.ax = this.sub16(this.reg.ax, this.fetchWord(), cf);
                break;
            }
            // ================================================================
            // PUSH/POP DS (1E/1F)
            // ================================================================
            case 0x1E:
                this.push(this.reg.ds);
                break;
            case 0x1F:
                this.reg.ds = this.pop();
                break;
            // ================================================================
            // AND (20-25)
            // ================================================================
            case 0x20: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const r = this.readRM8(mod, rm) & this.getReg8(reg);
                this.updateZSP8(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.writeRM8(mod, rm, r);
                break;
            }
            case 0x21: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const r = this.readRM16(mod, rm) & this.getReg16(reg);
                this.updateZSP16(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.writeRM16(mod, rm, r);
                break;
            }
            case 0x22: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const r = this.getReg8(reg) & this.readRM8(mod, rm);
                this.updateZSP8(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.setReg8(reg, r);
                break;
            }
            case 0x23: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const r = this.getReg16(reg) & this.readRM16(mod, rm);
                this.updateZSP16(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.setReg16(reg, r);
                break;
            }
            case 0x24: {
                const r = this.reg.al & this.fetchByte();
                this.updateZSP8(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.reg.al = r;
                break;
            }
            case 0x25: {
                const r = this.reg.ax & this.fetchWord();
                this.updateZSP16(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.reg.ax = r;
                break;
            }
            // ================================================================
            // DAA / DAS / AAA / AAS (27/2F/37/3F) - BCD
            // ================================================================
            case 0x27: { // DAA
                let al = this.reg.al;
                const oldAL = al, oldCF = this.reg.getFlag(FLAGS.CF);
                if ((al & 0x0F) > 9 || this.reg.getFlag(FLAGS.AF)) {
                    al += 6;
                    this.reg.setFlag(FLAGS.AF, true);
                }
                else {
                    this.reg.setFlag(FLAGS.AF, false);
                }
                if (oldAL > 0x99 || oldCF) {
                    al += 0x60;
                    this.reg.setFlag(FLAGS.CF, true);
                }
                else {
                    this.reg.setFlag(FLAGS.CF, false);
                }
                this.reg.al = al & 0xFF;
                this.updateZSP8(this.reg.al);
                break;
            }
            case 0x2F: { // DAS
                let al = this.reg.al;
                const oldAL = al, oldCF = this.reg.getFlag(FLAGS.CF);
                if ((al & 0x0F) > 9 || this.reg.getFlag(FLAGS.AF)) {
                    al -= 6;
                    this.reg.setFlag(FLAGS.AF, true);
                }
                else {
                    this.reg.setFlag(FLAGS.AF, false);
                }
                if (oldAL > 0x99 || oldCF) {
                    al -= 0x60;
                    this.reg.setFlag(FLAGS.CF, true);
                }
                else {
                    this.reg.setFlag(FLAGS.CF, false);
                }
                this.reg.al = al & 0xFF;
                this.updateZSP8(this.reg.al);
                break;
            }
            case 0x37: { // AAA
                if ((this.reg.al & 0x0F) > 9 || this.reg.getFlag(FLAGS.AF)) {
                    this.reg.al = (this.reg.al + 6) & 0xFF;
                    this.reg.ah = (this.reg.ah + 1) & 0xFF;
                    this.reg.setFlag(FLAGS.AF, true);
                    this.reg.setFlag(FLAGS.CF, true);
                }
                else {
                    this.reg.setFlag(FLAGS.AF, false);
                    this.reg.setFlag(FLAGS.CF, false);
                }
                this.reg.al &= 0x0F;
                break;
            }
            case 0x3F: { // AAS
                if ((this.reg.al & 0x0F) > 9 || this.reg.getFlag(FLAGS.AF)) {
                    this.reg.al = (this.reg.al - 6) & 0xFF;
                    this.reg.ah = (this.reg.ah - 1) & 0xFF;
                    this.reg.setFlag(FLAGS.AF, true);
                    this.reg.setFlag(FLAGS.CF, true);
                }
                else {
                    this.reg.setFlag(FLAGS.AF, false);
                    this.reg.setFlag(FLAGS.CF, false);
                }
                this.reg.al &= 0x0F;
                break;
            }
            // ================================================================
            // SUB (28-2D)
            // ================================================================
            case 0x28: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.writeRM8(mod, rm, this.sub8(this.readRM8(mod, rm), this.getReg8(reg)));
                break;
            }
            case 0x29: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.writeRM16(mod, rm, this.sub16(this.readRM16(mod, rm), this.getReg16(reg)));
                break;
            }
            case 0x2A: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.setReg8(reg, this.sub8(this.getReg8(reg), this.readRM8(mod, rm)));
                break;
            }
            case 0x2B: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.setReg16(reg, this.sub16(this.getReg16(reg), this.readRM16(mod, rm)));
                break;
            }
            case 0x2C:
                this.reg.al = this.sub8(this.reg.al, this.fetchByte());
                break;
            case 0x2D:
                this.reg.ax = this.sub16(this.reg.ax, this.fetchWord());
                break;
            // ================================================================
            // XOR (30-35)
            // ================================================================
            case 0x30: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const r = this.readRM8(mod, rm) ^ this.getReg8(reg);
                this.updateZSP8(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.writeRM8(mod, rm, r);
                break;
            }
            case 0x31: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const r = this.readRM16(mod, rm) ^ this.getReg16(reg);
                this.updateZSP16(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.writeRM16(mod, rm, r);
                break;
            }
            case 0x32: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const r = this.getReg8(reg) ^ this.readRM8(mod, rm);
                this.updateZSP8(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.setReg8(reg, r);
                break;
            }
            case 0x33: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const r = this.getReg16(reg) ^ this.readRM16(mod, rm);
                this.updateZSP16(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.setReg16(reg, r);
                break;
            }
            case 0x34: {
                const r = this.reg.al ^ this.fetchByte();
                this.updateZSP8(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.reg.al = r;
                break;
            }
            case 0x35: {
                const r = this.reg.ax ^ this.fetchWord();
                this.updateZSP16(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                this.reg.ax = r;
                break;
            }
            // ================================================================
            // CMP (38-3D)
            // ================================================================
            case 0x38: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.sub8(this.readRM8(mod, rm), this.getReg8(reg));
                break;
            }
            case 0x39: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.sub16(this.readRM16(mod, rm), this.getReg16(reg));
                break;
            }
            case 0x3A: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.sub8(this.getReg8(reg), this.readRM8(mod, rm));
                break;
            }
            case 0x3B: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.sub16(this.getReg16(reg), this.readRM16(mod, rm));
                break;
            }
            case 0x3C:
                this.sub8(this.reg.al, this.fetchByte());
                break;
            case 0x3D:
                this.sub16(this.reg.ax, this.fetchWord());
                break;
            // ================================================================
            // INC r16 (40-47) / DEC r16 (48-4F)
            // ================================================================
            case 0x40:
            case 0x41:
            case 0x42:
            case 0x43:
            case 0x44:
            case 0x45:
            case 0x46:
            case 0x47: {
                const r = opcode - 0x40, cf = this.reg.getFlag(FLAGS.CF);
                this.setReg16(r, this.add16(this.getReg16(r), 1));
                this.reg.setFlag(FLAGS.CF, cf);
                break;
            }
            case 0x48:
            case 0x49:
            case 0x4A:
            case 0x4B:
            case 0x4C:
            case 0x4D:
            case 0x4E:
            case 0x4F: {
                const r = opcode - 0x48, cf = this.reg.getFlag(FLAGS.CF);
                this.setReg16(r, this.sub16(this.getReg16(r), 1));
                this.reg.setFlag(FLAGS.CF, cf);
                break;
            }
            // ================================================================
            // PUSH r16 (50-57) / POP r16 (58-5F)
            // ================================================================
            case 0x50:
            case 0x51:
            case 0x52:
            case 0x53:
            case 0x54:
            case 0x55:
            case 0x56:
            case 0x57:
                this.push(this.getReg16(opcode - 0x50));
                break;
            case 0x58:
            case 0x59:
            case 0x5A:
            case 0x5B:
            case 0x5C:
            case 0x5D:
            case 0x5E:
            case 0x5F:
                this.setReg16(opcode - 0x58, this.pop());
                break;
            // ================================================================
            // PUSHA / POPA (60/61)
            // ================================================================
            case 0x60: { // PUSHA
                const sp = this.reg.sp;
                this.push(this.reg.ax);
                this.push(this.reg.cx);
                this.push(this.reg.dx);
                this.push(this.reg.bx);
                this.push(sp);
                this.push(this.reg.bp);
                this.push(this.reg.si);
                this.push(this.reg.di);
                break;
            }
            case 0x61: { // POPA
                this.reg.di = this.pop();
                this.reg.si = this.pop();
                this.reg.bp = this.pop();
                this.pop(); // SP discarded
                this.reg.bx = this.pop();
                this.reg.dx = this.pop();
                this.reg.cx = this.pop();
                this.reg.ax = this.pop();
                break;
            }
            // ================================================================
            // BOUND (62)
            // ================================================================
            case 0x62: { // BOUND r16, r/m16
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const ea = this.calcEA(mod, rm);
                const lower = this.mem.read16(ea);
                const upper = this.mem.read16(ea + 2);
                const val = this.getReg16(reg);
                if (val < lower || val > upper)
                    this.doInterrupt(5);
                break;
            }
            // ================================================================
            // PUSH imm16 (68) / IMUL r16,r/m16,imm (69) / PUSH imm8 (6A) / IMUL imm8 (6B)
            // ================================================================
            case 0x68:
                this.push(this.fetchWord());
                break;
            case 0x69: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const a = this.readRM16(mod, rm);
                const imm = this.fetchWord();
                const r = (this.toSigned16(a) * this.toSigned16(imm)) | 0;
                this.setReg16(reg, r & 0xFFFF);
                this.reg.setFlag(FLAGS.CF, r < -32768 || r > 32767);
                this.reg.setFlag(FLAGS.OF, r < -32768 || r > 32767);
                break;
            }
            case 0x6A:
                this.push(this.fetchSByte() & 0xFFFF);
                break;
            case 0x6B: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const a = this.readRM16(mod, rm);
                const imm = this.fetchSByte();
                const r = (this.toSigned16(a) * imm) | 0;
                this.setReg16(reg, r & 0xFFFF);
                this.reg.setFlag(FLAGS.CF, r < -32768 || r > 32767);
                this.reg.setFlag(FLAGS.OF, r < -32768 || r > 32767);
                break;
            }
            // ================================================================
            // 条件ジャンプ (70-7F)
            // ================================================================
            case 0x70: {
                const d = this.fetchSByte();
                if (this.reg.getFlag(FLAGS.OF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JO
            case 0x71: {
                const d = this.fetchSByte();
                if (!this.reg.getFlag(FLAGS.OF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JNO
            case 0x72: {
                const d = this.fetchSByte();
                if (this.reg.getFlag(FLAGS.CF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JB/JC
            case 0x73: {
                const d = this.fetchSByte();
                if (!this.reg.getFlag(FLAGS.CF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JAE/JNC
            case 0x74: {
                const d = this.fetchSByte();
                if (this.reg.getFlag(FLAGS.ZF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JE/JZ
            case 0x75: {
                const d = this.fetchSByte();
                if (!this.reg.getFlag(FLAGS.ZF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JNE/JNZ
            case 0x76: {
                const d = this.fetchSByte();
                if (this.reg.getFlag(FLAGS.CF) || this.reg.getFlag(FLAGS.ZF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JBE
            case 0x77: {
                const d = this.fetchSByte();
                if (!this.reg.getFlag(FLAGS.CF) && !this.reg.getFlag(FLAGS.ZF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JA
            case 0x78: {
                const d = this.fetchSByte();
                if (this.reg.getFlag(FLAGS.SF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JS
            case 0x79: {
                const d = this.fetchSByte();
                if (!this.reg.getFlag(FLAGS.SF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JNS
            case 0x7A: {
                const d = this.fetchSByte();
                if (this.reg.getFlag(FLAGS.PF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JP/JPE
            case 0x7B: {
                const d = this.fetchSByte();
                if (!this.reg.getFlag(FLAGS.PF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JNP/JPO
            case 0x7C: {
                const d = this.fetchSByte();
                if (this.reg.getFlag(FLAGS.SF) !== this.reg.getFlag(FLAGS.OF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JL
            case 0x7D: {
                const d = this.fetchSByte();
                if (this.reg.getFlag(FLAGS.SF) === this.reg.getFlag(FLAGS.OF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JGE
            case 0x7E: {
                const d = this.fetchSByte();
                if (this.reg.getFlag(FLAGS.ZF) || (this.reg.getFlag(FLAGS.SF) !== this.reg.getFlag(FLAGS.OF)))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JLE
            case 0x7F: {
                const d = this.fetchSByte();
                if (!this.reg.getFlag(FLAGS.ZF) && (this.reg.getFlag(FLAGS.SF) === this.reg.getFlag(FLAGS.OF)))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            } // JG
            // ================================================================
            // 80グループ: OP r/m8, imm8
            // ================================================================
            case 0x80: {
                const { mod, reg: op, rm } = decodeModRM(this.fetchByte());
                const a = this.readRM8(mod, rm);
                const imm = this.fetchByte();
                let r = 0;
                switch (op) {
                    case 0:
                        r = this.add8(a, imm);
                        this.writeRM8(mod, rm, r);
                        break;
                    case 1:
                        r = a | imm;
                        this.updateZSP8(r);
                        this.reg.setFlag(FLAGS.CF, false);
                        this.reg.setFlag(FLAGS.OF, false);
                        this.writeRM8(mod, rm, r);
                        break;
                    case 2:
                        r = this.add8(a, imm, this.reg.getFlag(FLAGS.CF) ? 1 : 0);
                        this.writeRM8(mod, rm, r);
                        break;
                    case 3:
                        r = this.sub8(a, imm, this.reg.getFlag(FLAGS.CF) ? 1 : 0);
                        this.writeRM8(mod, rm, r);
                        break;
                    case 4:
                        r = a & imm;
                        this.updateZSP8(r);
                        this.reg.setFlag(FLAGS.CF, false);
                        this.reg.setFlag(FLAGS.OF, false);
                        this.writeRM8(mod, rm, r);
                        break;
                    case 5:
                        r = this.sub8(a, imm);
                        this.writeRM8(mod, rm, r);
                        break;
                    case 6:
                        r = a ^ imm;
                        this.updateZSP8(r);
                        this.reg.setFlag(FLAGS.CF, false);
                        this.reg.setFlag(FLAGS.OF, false);
                        this.writeRM8(mod, rm, r);
                        break;
                    case 7:
                        this.sub8(a, imm);
                        break; // CMP
                }
                break;
            }
            // ================================================================
            // 81グループ: OP r/m16, imm16
            // ================================================================
            case 0x81: {
                const { mod, reg: op, rm } = decodeModRM(this.fetchByte());
                const a = this.readRM16(mod, rm);
                const imm = this.fetchWord();
                let r = 0;
                switch (op) {
                    case 0:
                        r = this.add16(a, imm);
                        this.writeRM16(mod, rm, r);
                        break;
                    case 1:
                        r = a | imm;
                        this.updateZSP16(r);
                        this.reg.setFlag(FLAGS.CF, false);
                        this.reg.setFlag(FLAGS.OF, false);
                        this.writeRM16(mod, rm, r);
                        break;
                    case 2:
                        r = this.add16(a, imm, this.reg.getFlag(FLAGS.CF) ? 1 : 0);
                        this.writeRM16(mod, rm, r);
                        break;
                    case 3:
                        r = this.sub16(a, imm, this.reg.getFlag(FLAGS.CF) ? 1 : 0);
                        this.writeRM16(mod, rm, r);
                        break;
                    case 4:
                        r = a & imm;
                        this.updateZSP16(r);
                        this.reg.setFlag(FLAGS.CF, false);
                        this.reg.setFlag(FLAGS.OF, false);
                        this.writeRM16(mod, rm, r);
                        break;
                    case 5:
                        r = this.sub16(a, imm);
                        this.writeRM16(mod, rm, r);
                        break;
                    case 6:
                        r = a ^ imm;
                        this.updateZSP16(r);
                        this.reg.setFlag(FLAGS.CF, false);
                        this.reg.setFlag(FLAGS.OF, false);
                        this.writeRM16(mod, rm, r);
                        break;
                    case 7:
                        this.sub16(a, imm);
                        break; // CMP
                }
                break;
            }
            // ================================================================
            // 83グループ: OP r/m16, imm8 (sign-extend)
            // ================================================================
            case 0x83: {
                const { mod, reg: op, rm } = decodeModRM(this.fetchByte());
                const a = this.readRM16(mod, rm);
                const imm = this.fetchSByte() & 0xFFFF;
                let r = 0;
                switch (op) {
                    case 0:
                        r = this.add16(a, imm);
                        this.writeRM16(mod, rm, r);
                        break;
                    case 1:
                        r = a | imm;
                        this.updateZSP16(r);
                        this.reg.setFlag(FLAGS.CF, false);
                        this.reg.setFlag(FLAGS.OF, false);
                        this.writeRM16(mod, rm, r);
                        break;
                    case 2:
                        r = this.add16(a, imm, this.reg.getFlag(FLAGS.CF) ? 1 : 0);
                        this.writeRM16(mod, rm, r);
                        break;
                    case 3:
                        r = this.sub16(a, imm, this.reg.getFlag(FLAGS.CF) ? 1 : 0);
                        this.writeRM16(mod, rm, r);
                        break;
                    case 4:
                        r = a & imm;
                        this.updateZSP16(r);
                        this.reg.setFlag(FLAGS.CF, false);
                        this.reg.setFlag(FLAGS.OF, false);
                        this.writeRM16(mod, rm, r);
                        break;
                    case 5:
                        r = this.sub16(a, imm);
                        this.writeRM16(mod, rm, r);
                        break;
                    case 6:
                        r = a ^ imm;
                        this.updateZSP16(r);
                        this.reg.setFlag(FLAGS.CF, false);
                        this.reg.setFlag(FLAGS.OF, false);
                        this.writeRM16(mod, rm, r);
                        break;
                    case 7:
                        this.sub16(a, imm);
                        break; // CMP
                }
                break;
            }
            // ================================================================
            // TEST (84/85)
            // ================================================================
            case 0x84: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const r = this.readRM8(mod, rm) & this.getReg8(reg);
                this.updateZSP8(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                break;
            }
            case 0x85: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const r = this.readRM16(mod, rm) & this.getReg16(reg);
                this.updateZSP16(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                break;
            }
            // ================================================================
            // XCHG (86/87)
            // ================================================================
            case 0x86: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const a = this.getReg8(reg);
                const b = this.readRM8(mod, rm);
                this.setReg8(reg, b);
                this.writeRM8(mod, rm, a);
                break;
            }
            case 0x87: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const a = this.getReg16(reg);
                const b = this.readRM16(mod, rm);
                this.setReg16(reg, b);
                this.writeRM16(mod, rm, a);
                break;
            }
            // ================================================================
            // MOV (88-8B)
            // ================================================================
            case 0x88: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.writeRM8(mod, rm, this.getReg8(reg));
                break;
            }
            case 0x89: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.writeRM16(mod, rm, this.getReg16(reg));
                break;
            }
            case 0x8A: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.setReg8(reg, this.readRM8(mod, rm));
                break;
            }
            case 0x8B: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.setReg16(reg, this.readRM16(mod, rm));
                break;
            }
            // ================================================================
            // MOV sreg (8C/8E) / LEA (8D) / POP r/m16 (8F)
            // ================================================================
            case 0x8C: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.writeRM16(mod, rm, this.getSegReg(reg));
                break;
            }
            case 0x8D: { // LEA
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const ea = this.calcEAOffsetOnly(mod, rm);
                this.setReg16(reg, ea);
                break;
            }
            case 0x8E: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.setSegReg(reg, this.readRM16(mod, rm));
                break;
            }
            case 0x8F: {
                const { mod, rm } = decodeModRM(this.fetchByte());
                this.writeRM16(mod, rm, this.pop());
                break;
            } // POP r/m16
            // ================================================================
            // NOP / XCHG AX,rX (90-97)
            // ================================================================
            case 0x90: break; // NOP
            case 0x91:
            case 0x92:
            case 0x93:
            case 0x94:
            case 0x95:
            case 0x96:
            case 0x97: {
                const r = opcode - 0x90;
                const t = this.reg.ax;
                this.reg.ax = this.getReg16(r);
                this.setReg16(r, t);
                break;
            }
            // ================================================================
            // CBW / CWD (98/99)
            // ================================================================
            case 0x98:
                this.reg.ax = this.reg.al >= 0x80 ? 0xFF00 | this.reg.al : this.reg.al;
                break;
            case 0x99:
                this.reg.dx = this.reg.ax >= 0x8000 ? 0xFFFF : 0;
                break;
            // ================================================================
            // CALL far (9A)
            // ================================================================
            case 0x9A: {
                const newIP = this.fetchWord(), newCS = this.fetchWord();
                this.push(this.reg.cs);
                this.push(this.reg.ip);
                this.reg.cs = newCS;
                this.reg.ip = newIP;
                break;
            }
            // ================================================================
            // PUSHF / POPF / LAHF / SAHF (9C-9F)
            // ================================================================
            case 0x9C:
                this.push(this.reg.flags);
                break;
            case 0x9D:
                this.reg.flags = (this.pop() & 0x0FD5) | 0x0002;
                break;
            case 0x9B: break; // WAIT/FWAIT (NOP - FPU not implemented)
            case 0x9E:
                this.reg.flags = (this.reg.flags & 0xFF00) | (this.reg.ah & 0xD5) | 0x02;
                break; // SAHF
            case 0x9F:
                this.reg.ah = this.reg.flags & 0xFF;
                break; // LAHF
            // ================================================================
            // MOV AL/AX,[imm16] / [imm16],AL/AX (A0-A3)
            // ================================================================
            case 0xA0:
                this.reg.al = this.mem.read8(this.segAddr(this.reg.ds, this.fetchWord()));
                break;
            case 0xA1:
                this.reg.ax = this.mem.read16(this.segAddr(this.reg.ds, this.fetchWord()));
                break;
            case 0xA2:
                this.mem.write8(this.segAddr(this.reg.ds, this.fetchWord()), this.reg.al);
                break;
            case 0xA3:
                this.mem.write16(this.segAddr(this.reg.ds, this.fetchWord()), this.reg.ax);
                break;
            // ================================================================
            // 文字列命令 (A4-AF) + REP対応
            // ================================================================
            case 0xA4: { // MOVSB
                this._lastStrOpSetsZF = false;
                this.strStep(() => {
                    const v = this.mem.read8(this.segAddr(this.reg.ds, this.reg.si));
                    this.mem.write8(this.reg.segmented(this.reg.es, this.reg.di), v);
                    const d = this.siDir();
                    this.reg.si = (this.reg.si + d) & 0xFFFF;
                    this.reg.di = (this.reg.di + d) & 0xFFFF;
                });
                break;
            }
            case 0xA5: { // MOVSW
                this._lastStrOpSetsZF = false;
                this.strStep(() => {
                    const v = this.mem.read16(this.segAddr(this.reg.ds, this.reg.si));
                    this.mem.write16(this.reg.segmented(this.reg.es, this.reg.di), v);
                    const d = this.siDir() * 2;
                    this.reg.si = (this.reg.si + d) & 0xFFFF;
                    this.reg.di = (this.reg.di + d) & 0xFFFF;
                });
                break;
            }
            case 0xA6: { // CMPSB
                this._lastStrOpSetsZF = true;
                this.strStep(() => {
                    const a = this.mem.read8(this.segAddr(this.reg.ds, this.reg.si));
                    const b = this.mem.read8(this.reg.segmented(this.reg.es, this.reg.di));
                    this.sub8(a, b);
                    const d = this.siDir();
                    this.reg.si = (this.reg.si + d) & 0xFFFF;
                    this.reg.di = (this.reg.di + d) & 0xFFFF;
                });
                break;
            }
            case 0xA7: { // CMPSW
                this._lastStrOpSetsZF = true;
                this.strStep(() => {
                    const a = this.mem.read16(this.segAddr(this.reg.ds, this.reg.si));
                    const b = this.mem.read16(this.reg.segmented(this.reg.es, this.reg.di));
                    this.sub16(a, b);
                    const d = this.siDir() * 2;
                    this.reg.si = (this.reg.si + d) & 0xFFFF;
                    this.reg.di = (this.reg.di + d) & 0xFFFF;
                });
                break;
            }
            case 0xA8: {
                const r = this.reg.al & this.fetchByte();
                this.updateZSP8(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                break;
            } // TEST AL,imm8
            case 0xA9: {
                const r = this.reg.ax & this.fetchWord();
                this.updateZSP16(r);
                this.reg.setFlag(FLAGS.CF, false);
                this.reg.setFlag(FLAGS.OF, false);
                break;
            } // TEST AX,imm16
            case 0xAA: { // STOSB
                this._lastStrOpSetsZF = false;
                this.strStep(() => {
                    this.mem.write8(this.reg.segmented(this.reg.es, this.reg.di), this.reg.al);
                    this.reg.di = (this.reg.di + this.siDir()) & 0xFFFF;
                });
                break;
            }
            case 0xAB: { // STOSW
                this._lastStrOpSetsZF = false;
                this.strStep(() => {
                    this.mem.write16(this.reg.segmented(this.reg.es, this.reg.di), this.reg.ax);
                    this.reg.di = (this.reg.di + this.siDir() * 2) & 0xFFFF;
                });
                break;
            }
            case 0xAC: { // LODSB
                this._lastStrOpSetsZF = false;
                this.strStep(() => {
                    this.reg.al = this.mem.read8(this.segAddr(this.reg.ds, this.reg.si));
                    this.reg.si = (this.reg.si + this.siDir()) & 0xFFFF;
                });
                break;
            }
            case 0xAD: { // LODSW
                this._lastStrOpSetsZF = false;
                this.strStep(() => {
                    this.reg.ax = this.mem.read16(this.segAddr(this.reg.ds, this.reg.si));
                    this.reg.si = (this.reg.si + this.siDir() * 2) & 0xFFFF;
                });
                break;
            }
            case 0xAE: { // SCASB
                this._lastStrOpSetsZF = true;
                this.strStep(() => {
                    const b = this.mem.read8(this.reg.segmented(this.reg.es, this.reg.di));
                    this.sub8(this.reg.al, b);
                    this.reg.di = (this.reg.di + this.siDir()) & 0xFFFF;
                });
                break;
            }
            case 0xAF: { // SCASW
                this._lastStrOpSetsZF = true;
                this.strStep(() => {
                    const b = this.mem.read16(this.reg.segmented(this.reg.es, this.reg.di));
                    this.sub16(this.reg.ax, b);
                    this.reg.di = (this.reg.di + this.siDir() * 2) & 0xFFFF;
                });
                break;
            }
            // ================================================================
            // MOV r8,imm8 (B0-B7) / MOV r16,imm16 (B8-BF)
            // ================================================================
            case 0xB0:
            case 0xB1:
            case 0xB2:
            case 0xB3:
            case 0xB4:
            case 0xB5:
            case 0xB6:
            case 0xB7:
                this.setReg8(opcode - 0xB0, this.fetchByte());
                break;
            case 0xB8:
            case 0xB9:
            case 0xBA:
            case 0xBB:
            case 0xBC:
            case 0xBD:
            case 0xBE:
            case 0xBF:
                this.setReg16(opcode - 0xB8, this.fetchWord());
                break;
            // ================================================================
            // C0/C1: シフトグループ imm8
            // ================================================================
            case 0xC0: {
                const { mod, reg: op, rm } = decodeModRM(this.fetchByte());
                const cnt = this.fetchByte() & 0x1F;
                const v = this.readRM8(mod, rm);
                this.writeRM8(mod, rm, this.doShift8(op, v, cnt));
                break;
            }
            case 0xC1: {
                const { mod, reg: op, rm } = decodeModRM(this.fetchByte());
                const cnt = this.fetchByte() & 0x1F;
                const v = this.readRM16(mod, rm);
                this.writeRM16(mod, rm, this.doShift16(op, v, cnt));
                break;
            }
            // ================================================================
            // RET (C2/C3/CA/CB)
            // ================================================================
            case 0xC2: {
                const n = this.fetchWord();
                this.reg.ip = this.pop();
                this.reg.sp = (this.reg.sp + n) & 0xFFFF;
                break;
            }
            case 0xC3:
                this.reg.ip = this.pop();
                break;
            case 0xCA: {
                const n = this.fetchWord();
                this.reg.ip = this.pop();
                this.reg.cs = this.pop();
                this.reg.sp = (this.reg.sp + n) & 0xFFFF;
                break;
            }
            case 0xCB:
                this.reg.ip = this.pop();
                this.reg.cs = this.pop();
                break;
            // ================================================================
            // LES / LDS (C4/C5)
            // ================================================================
            case 0xC4: { // LES r16, m16:16
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const ea = this.calcEA(mod, rm);
                this.setReg16(reg, this.mem.read16(ea));
                this.reg.es = this.mem.read16(ea + 2);
                break;
            }
            case 0xC5: { // LDS r16, m16:16
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const ea = this.calcEA(mod, rm);
                this.setReg16(reg, this.mem.read16(ea));
                this.reg.ds = this.mem.read16(ea + 2);
                break;
            }
            // ================================================================
            // MOV r/m8,imm8 / MOV r/m16,imm16 (C6/C7)
            // ================================================================
            case 0xC6: {
                const { mod, rm } = decodeModRM(this.fetchByte());
                if (mod !== 3)
                    this.calcEA(mod, rm); // EA計算を先にやる（dispフェッチ）
                const imm = this.fetchByte();
                if (mod === 3)
                    this.setReg8(rm, imm);
                else
                    this.mem.write8(this._lastEA, imm);
                break;
            }
            case 0xC7: {
                const { mod, rm } = decodeModRM(this.fetchByte());
                if (mod !== 3)
                    this.calcEA(mod, rm); // EA計算を先にやる（dispフェッチ）
                const imm = this.fetchWord();
                if (mod === 3)
                    this.setReg16(rm, imm);
                else
                    this.mem.write16(this._lastEA, imm);
                break;
            }
            // ================================================================
            // ENTER / LEAVE (C8/C9)
            // ================================================================
            case 0xC8: { // ENTER imm16, imm8
                const size = this.fetchWord();
                const level = this.fetchByte() & 0x1F;
                this.push(this.reg.bp);
                const frameBP = this.reg.sp;
                if (level > 0) {
                    let bp = this.reg.bp;
                    for (let i = 1; i < level; i++) {
                        bp = (bp - 2) & 0xFFFF;
                        this.push(this.mem.read16(this.reg.segmented(this.reg.ss, bp)));
                    }
                    this.push(frameBP);
                }
                this.reg.bp = frameBP;
                this.reg.sp = (this.reg.sp - size) & 0xFFFF;
                break;
            }
            case 0xC9: { // LEAVE
                this.reg.sp = this.reg.bp;
                this.reg.bp = this.pop();
                break;
            }
            // ================================================================
            // INT 3 / INT n / INTO / IRET (CC/CD/CE/CF)
            // ================================================================
            case 0xCC: // INT 3
                this.push(this.reg.flags);
                this.push(this.reg.cs);
                this.push(this.reg.ip);
                this.reg.setFlag(FLAGS.IF, false);
                this.doInterrupt(3);
                break;
            case 0xCD: { // INT n
                const vec = this.fetchByte();
                this.push(this.reg.flags);
                this.push(this.reg.cs);
                this.push(this.reg.ip);
                this.reg.setFlag(FLAGS.IF, false);
                this.doInterrupt(vec);
                break;
            }
            case 0xCE: // INTO
                if (this.reg.getFlag(FLAGS.OF)) {
                    this.push(this.reg.flags);
                    this.push(this.reg.cs);
                    this.push(this.reg.ip);
                    this.doInterrupt(4);
                }
                break;
            case 0xCF: // IRET
                this.reg.ip = this.pop();
                this.reg.cs = this.pop();
                this.reg.flags = (this.pop() & 0x0FD5) | 0x0002;
                break;
            // ================================================================
            // D0/D1: シフトグループ count=1
            // ================================================================
            case 0xD0: {
                const { mod, reg: op, rm } = decodeModRM(this.fetchByte());
                this.writeRM8(mod, rm, this.doShift8(op, this.readRM8(mod, rm), 1));
                break;
            }
            case 0xD1: {
                const { mod, reg: op, rm } = decodeModRM(this.fetchByte());
                this.writeRM16(mod, rm, this.doShift16(op, this.readRM16(mod, rm), 1));
                break;
            }
            // D2/D3: シフトグループ count=CL
            case 0xD2: {
                const { mod, reg: op, rm } = decodeModRM(this.fetchByte());
                this.writeRM8(mod, rm, this.doShift8(op, this.readRM8(mod, rm), this.reg.cl));
                break;
            }
            case 0xD3: {
                const { mod, reg: op, rm } = decodeModRM(this.fetchByte());
                this.writeRM16(mod, rm, this.doShift16(op, this.readRM16(mod, rm), this.reg.cl));
                break;
            }
            // ================================================================
            // AAM / AAD (D4/D5) - BCD
            // ================================================================
            case 0xD4: { // AAM
                const base = this.fetchByte();
                if (base === 0) {
                    this.doInterrupt(0);
                    break;
                }
                this.reg.ah = Math.floor(this.reg.al / base) & 0xFF;
                this.reg.al = (this.reg.al % base) & 0xFF;
                this.updateZSP8(this.reg.al);
                break;
            }
            case 0xD5: { // AAD
                const base = this.fetchByte();
                this.reg.al = ((this.reg.ah * base) + this.reg.al) & 0xFF;
                this.reg.ah = 0;
                this.updateZSP8(this.reg.al);
                break;
            }
            // ================================================================
            // XLAT (D7)
            // ================================================================
            case 0xD7: {
                const addr = this.segAddr(this.reg.ds, (this.reg.bx + this.reg.al) & 0xFFFF);
                this.reg.al = this.mem.read8(addr);
                break;
            }
            // ================================================================
            // ESC (D8-DF) - FPU (ignore / stub)
            // ================================================================
            case 0xD8:
            case 0xD9:
            case 0xDA:
            case 0xDB:
            case 0xDC:
            case 0xDD:
            case 0xDE:
            case 0xDF: {
                const { mod, rm } = decodeModRM(this.fetchByte());
                if (mod !== 3)
                    this.calcEA(mod, rm); // ディスプレースメントも消費
                break;
            }
            // ================================================================
            // LOOPNE / LOOPE / LOOP / JCXZ (E0-E3)
            // ================================================================
            case 0xE0: { // LOOPNE
                const d = this.fetchSByte();
                this.reg.cx = (this.reg.cx - 1) & 0xFFFF;
                if (this.reg.cx !== 0 && !this.reg.getFlag(FLAGS.ZF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0xE1: { // LOOPE
                const d = this.fetchSByte();
                this.reg.cx = (this.reg.cx - 1) & 0xFFFF;
                if (this.reg.cx !== 0 && this.reg.getFlag(FLAGS.ZF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0xE2: { // LOOP
                const d = this.fetchSByte();
                this.reg.cx = (this.reg.cx - 1) & 0xFFFF;
                if (this.reg.cx !== 0)
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0xE3: { // JCXZ
                const d = this.fetchSByte();
                if (this.reg.cx === 0)
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            // ================================================================
            // IN / OUT (E4-E7 / EC-EF)
            // ================================================================
            case 0xE4:
                this.reg.al = this.ioRead(this.fetchByte());
                break;
            case 0xE5: {
                const p = this.fetchByte();
                this.reg.ax = this.ioRead(p) | (this.ioRead(p + 1) << 8);
                break;
            }
            case 0xE6:
                this.ioWrite(this.fetchByte(), this.reg.al);
                break;
            case 0xE7: {
                const p = this.fetchByte();
                this.ioWrite(p, this.reg.al);
                this.ioWrite(p + 1, this.reg.ah);
                break;
            }
            case 0xEC:
                this.reg.al = this.ioRead(this.reg.dx);
                break;
            case 0xED:
                this.reg.ax = this.ioRead(this.reg.dx) | (this.ioRead(this.reg.dx + 1) << 8);
                break;
            case 0xEE:
                this.ioWrite(this.reg.dx, this.reg.al);
                break;
            case 0xEF:
                this.ioWrite(this.reg.dx, this.reg.al);
                this.ioWrite(this.reg.dx + 1, this.reg.ah);
                break;
            // ================================================================
            // CALL near / JMP near / JMP short / JMP far (E8/E9/EB/EA)
            // ================================================================
            case 0xE8: {
                const d = this.fetchSWord();
                this.push(this.reg.ip);
                this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0xE9: {
                const d = this.fetchSWord();
                this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0xEA: {
                const ip = this.fetchWord(), cs = this.fetchWord();
                this.reg.ip = ip;
                this.reg.cs = cs;
                break;
            }
            case 0xEB: {
                const d = this.fetchSByte();
                this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            // ================================================================
            // HLT (F4)
            // ================================================================
            case 0xF4:
                this.halted = true;
                this.haltReason = 'hlt';
                break;
            // ================================================================
            // フラグ操作 (F5/F8/F9/FA/FB/FC/FD)
            // ================================================================
            case 0xF5:
                this.reg.setFlag(FLAGS.CF, !this.reg.getFlag(FLAGS.CF));
                break; // CMC
            case 0xF8:
                this.reg.setFlag(FLAGS.CF, false);
                break; // CLC
            case 0xF9:
                this.reg.setFlag(FLAGS.CF, true);
                break; // STC
            case 0xFA:
                this.reg.setFlag(FLAGS.IF, false);
                break; // CLI
            case 0xFB:
                this.reg.setFlag(FLAGS.IF, true);
                break; // STI
            case 0xFC:
                this.reg.setFlag(FLAGS.DF, false);
                break; // CLD
            case 0xFD:
                this.reg.setFlag(FLAGS.DF, true);
                break; // STD
            // ================================================================
            // F6グループ: TEST/NOT/NEG/MUL/IMUL/DIV/IDIV r/m8
            // ================================================================
            case 0xF6: {
                const { mod, reg: op, rm } = decodeModRM(this.fetchByte());
                const a = this.readRM8(mod, rm);
                switch (op) {
                    case 0:
                    case 1: { // TEST r/m8, imm8
                        const imm = this.fetchByte();
                        const r = a & imm;
                        this.updateZSP8(r);
                        this.reg.setFlag(FLAGS.CF, false);
                        this.reg.setFlag(FLAGS.OF, false);
                        break;
                    }
                    case 2:
                        this.writeRM8(mod, rm, (~a) & 0xFF);
                        break; // NOT
                    case 3: { // NEG
                        const r = this.sub8(0, a);
                        this.writeRM8(mod, rm, r);
                        this.reg.setFlag(FLAGS.CF, a !== 0);
                        break;
                    }
                    case 4: { // MUL r/m8  → AX = AL * r/m8
                        const result = this.reg.al * a;
                        this.reg.ax = result & 0xFFFF;
                        const overflow = this.reg.ah !== 0;
                        this.reg.setFlag(FLAGS.CF, overflow);
                        this.reg.setFlag(FLAGS.OF, overflow);
                        break;
                    }
                    case 5: { // IMUL r/m8 → AX = AL * r/m8 (signed)
                        const result = this.toSigned8(this.reg.al) * this.toSigned8(a);
                        this.reg.ax = result & 0xFFFF;
                        const overflow = result < -128 || result > 127;
                        this.reg.setFlag(FLAGS.CF, overflow);
                        this.reg.setFlag(FLAGS.OF, overflow);
                        break;
                    }
                    case 6: { // DIV r/m8  → AL=AX/r/m8, AH=AX%r/m8
                        if (a === 0) {
                            this.doInterrupt(0);
                            break;
                        }
                        const dividend6 = this.reg.ax;
                        const q = Math.floor(dividend6 / a);
                        if (q > 0xFF) {
                            this.doInterrupt(0);
                            break;
                        }
                        this.reg.al = q & 0xFF;
                        this.reg.ah = (dividend6 % a) & 0xFF;
                        break;
                    }
                    case 7: { // IDIV r/m8
                        if (a === 0) {
                            this.doInterrupt(0);
                            break;
                        }
                        const dividend = this.toSigned16(this.reg.ax);
                        const divisor = this.toSigned8(a);
                        const q = Math.trunc(dividend / divisor);
                        if (q < -128 || q > 127) {
                            this.doInterrupt(0);
                            break;
                        }
                        this.reg.al = q & 0xFF;
                        this.reg.ah = (dividend % divisor) & 0xFF;
                        break;
                    }
                }
                break;
            }
            // ================================================================
            // F7グループ: TEST/NOT/NEG/MUL/IMUL/DIV/IDIV r/m16
            // ================================================================
            case 0xF7: {
                const { mod, reg: op, rm } = decodeModRM(this.fetchByte());
                const a = this.readRM16(mod, rm);
                switch (op) {
                    case 0:
                    case 1: { // TEST r/m16, imm16
                        const imm = this.fetchWord();
                        const r = a & imm;
                        this.updateZSP16(r);
                        this.reg.setFlag(FLAGS.CF, false);
                        this.reg.setFlag(FLAGS.OF, false);
                        break;
                    }
                    case 2:
                        this.writeRM16(mod, rm, (~a) & 0xFFFF);
                        break; // NOT
                    case 3: { // NEG
                        const r = this.sub16(0, a);
                        this.writeRM16(mod, rm, r);
                        this.reg.setFlag(FLAGS.CF, a !== 0);
                        break;
                    }
                    case 4: { // MUL r/m16 → DX:AX = AX * r/m16
                        const result = this.reg.ax * a;
                        this.reg.ax = result & 0xFFFF;
                        this.reg.dx = Math.trunc(result / 0x10000) & 0xFFFF;
                        const overflow = this.reg.dx !== 0;
                        this.reg.setFlag(FLAGS.CF, overflow);
                        this.reg.setFlag(FLAGS.OF, overflow);
                        break;
                    }
                    case 5: { // IMUL r/m16 → DX:AX = AX * r/m16 (signed)
                        const result = this.toSigned16(this.reg.ax) * this.toSigned16(a);
                        this.reg.ax = result & 0xFFFF;
                        this.reg.dx = Math.trunc(result / 0x10000) & 0xFFFF;
                        const overflow = result < -32768 || result > 32767;
                        this.reg.setFlag(FLAGS.CF, overflow);
                        this.reg.setFlag(FLAGS.OF, overflow);
                        break;
                    }
                    case 6: { // DIV r/m16 → AX=DX:AX/r/m16, DX=余り
                        if (a === 0) {
                            this.doInterrupt(0);
                            break;
                        }
                        const dividend = this.reg.dx * 0x10000 + this.reg.ax;
                        const q = Math.floor(dividend / a);
                        if (q > 0xFFFF) {
                            this.doInterrupt(0);
                            break;
                        }
                        this.reg.ax = q & 0xFFFF;
                        this.reg.dx = (dividend % a) & 0xFFFF;
                        break;
                    }
                    case 7: { // IDIV r/m16
                        if (a === 0) {
                            this.doInterrupt(0);
                            break;
                        }
                        const dividend = this.toSigned32(this.reg.dx * 0x10000 + this.reg.ax);
                        const divisor = this.toSigned16(a);
                        const q = Math.trunc(dividend / divisor);
                        if (q < -32768 || q > 32767) {
                            this.doInterrupt(0);
                            break;
                        }
                        this.reg.ax = q & 0xFFFF;
                        this.reg.dx = (dividend % divisor) & 0xFFFF;
                        break;
                    }
                }
                break;
            }
            // ================================================================
            // FE グループ: INC/DEC r/m8
            // ================================================================
            case 0xFE: {
                const { mod, reg: op, rm } = decodeModRM(this.fetchByte());
                const cf = this.reg.getFlag(FLAGS.CF);
                if (op === 0) { // INC
                    this.writeRM8(mod, rm, this.add8(this.readRM8(mod, rm), 1));
                }
                else { // DEC
                    this.writeRM8(mod, rm, this.sub8(this.readRM8(mod, rm), 1));
                }
                this.reg.setFlag(FLAGS.CF, cf);
                break;
            }
            // ================================================================
            // FF グループ: INC/DEC/CALL/JMP/PUSH r/m16
            // ================================================================
            case 0xFF: {
                const { mod, reg: op, rm } = decodeModRM(this.fetchByte());
                const cf = this.reg.getFlag(FLAGS.CF);
                switch (op) {
                    case 0: { // INC r/m16
                        this.writeRM16(mod, rm, this.add16(this.readRM16(mod, rm), 1));
                        this.reg.setFlag(FLAGS.CF, cf);
                        break;
                    }
                    case 1: { // DEC r/m16
                        this.writeRM16(mod, rm, this.sub16(this.readRM16(mod, rm), 1));
                        this.reg.setFlag(FLAGS.CF, cf);
                        break;
                    }
                    case 2: { // CALL r/m16
                        const target = this.readRM16(mod, rm);
                        this.push(this.reg.ip);
                        this.reg.ip = target;
                        break;
                    }
                    case 3: { // CALL far m16:16
                        const ea = this.calcEA(mod, rm);
                        this.push(this.reg.cs);
                        this.push(this.reg.ip);
                        this.reg.ip = this.mem.read16(ea);
                        this.reg.cs = this.mem.read16(ea + 2);
                        break;
                    }
                    case 4: { // JMP r/m16
                        this.reg.ip = this.readRM16(mod, rm);
                        break;
                    }
                    case 5: { // JMP far m16:16
                        const ea = this.calcEA(mod, rm);
                        this.reg.ip = this.mem.read16(ea);
                        this.reg.cs = this.mem.read16(ea + 2);
                        break;
                    }
                    case 6: { // PUSH r/m16
                        this.push(this.readRM16(mod, rm));
                        break;
                    }
                }
                break;
            }
            default:
                if (this.debugMode) {
                    this.debugLog.push(`UNKNOWN: 0x${opcode.toString(16).padStart(2, '0')} at CS:IP=${this.reg.cs.toString(16)}:${((this.reg.ip - 1) & 0xFFFF).toString(16)}`);
                }
                break;
        }
    }
    // ================================================================
    // 0F プレフィックス命令
    // ================================================================
    exec0F() {
        const op2 = this.fetchByte();
        switch (op2) {
            // 条件ジャンプ near (0F 80-8F)
            case 0x80: {
                const d = this.fetchSWord();
                if (this.reg.getFlag(FLAGS.OF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x81: {
                const d = this.fetchSWord();
                if (!this.reg.getFlag(FLAGS.OF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x82: {
                const d = this.fetchSWord();
                if (this.reg.getFlag(FLAGS.CF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x83: {
                const d = this.fetchSWord();
                if (!this.reg.getFlag(FLAGS.CF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x84: {
                const d = this.fetchSWord();
                if (this.reg.getFlag(FLAGS.ZF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x85: {
                const d = this.fetchSWord();
                if (!this.reg.getFlag(FLAGS.ZF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x86: {
                const d = this.fetchSWord();
                if (this.reg.getFlag(FLAGS.CF) || this.reg.getFlag(FLAGS.ZF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x87: {
                const d = this.fetchSWord();
                if (!this.reg.getFlag(FLAGS.CF) && !this.reg.getFlag(FLAGS.ZF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x88: {
                const d = this.fetchSWord();
                if (this.reg.getFlag(FLAGS.SF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x89: {
                const d = this.fetchSWord();
                if (!this.reg.getFlag(FLAGS.SF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x8A: {
                const d = this.fetchSWord();
                if (this.reg.getFlag(FLAGS.PF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x8B: {
                const d = this.fetchSWord();
                if (!this.reg.getFlag(FLAGS.PF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x8C: {
                const d = this.fetchSWord();
                if (this.reg.getFlag(FLAGS.SF) !== this.reg.getFlag(FLAGS.OF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x8D: {
                const d = this.fetchSWord();
                if (this.reg.getFlag(FLAGS.SF) === this.reg.getFlag(FLAGS.OF))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x8E: {
                const d = this.fetchSWord();
                if (this.reg.getFlag(FLAGS.ZF) || (this.reg.getFlag(FLAGS.SF) !== this.reg.getFlag(FLAGS.OF)))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            case 0x8F: {
                const d = this.fetchSWord();
                if (!this.reg.getFlag(FLAGS.ZF) && (this.reg.getFlag(FLAGS.SF) === this.reg.getFlag(FLAGS.OF)))
                    this.reg.ip = (this.reg.ip + d) & 0xFFFF;
                break;
            }
            // IMUL r16, r/m16 (0F AF)
            case 0xAF: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const a = this.toSigned16(this.getReg16(reg));
                const b = this.toSigned16(this.readRM16(mod, rm));
                const r = (a * b) | 0;
                this.setReg16(reg, r & 0xFFFF);
                const overflow = r < -32768 || r > 32767;
                this.reg.setFlag(FLAGS.CF, overflow);
                this.reg.setFlag(FLAGS.OF, overflow);
                break;
            }
            // MOVZX r16, r/m8 (0F B6)
            case 0xB6: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.setReg16(reg, this.readRM8(mod, rm));
                break;
            }
            // MOVSX r16, r/m8 (0F BE)
            case 0xBE: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                this.setReg16(reg, this.toSigned8(this.readRM8(mod, rm)) & 0xFFFF);
                break;
            }
            // BSF / BSR (0F BC / BD) - ビットスキャン
            case 0xBC: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const v = this.readRM16(mod, rm);
                if (v === 0) {
                    this.reg.setFlag(FLAGS.ZF, true);
                    break;
                }
                let i = 0;
                while ((v & (1 << i)) === 0)
                    i++;
                this.setReg16(reg, i);
                this.reg.setFlag(FLAGS.ZF, false);
                break;
            }
            case 0xBD: {
                const { mod, reg, rm } = decodeModRM(this.fetchByte());
                const v = this.readRM16(mod, rm);
                if (v === 0) {
                    this.reg.setFlag(FLAGS.ZF, true);
                    break;
                }
                let i = 15;
                while ((v & (1 << i)) === 0)
                    i--;
                this.setReg16(reg, i);
                this.reg.setFlag(FLAGS.ZF, false);
                break;
            }
            default:
                if (this.debugMode)
                    this.debugLog.push(`UNKNOWN 0F ${op2.toString(16)}`);
                break;
            // PUSH FS (0F A0) / POP FS (0F A1)
            case 0xA0:
                this.push(this.reg.fs);
                break;
            case 0xA1:
                this.reg.fs = this.pop();
                break;
            // PUSH GS (0F A8) / POP GS (0F A9)
            case 0xA8:
                this.push(this.reg.gs);
                break;
            case 0xA9:
                this.reg.gs = this.pop();
                break;
        }
    }
    // ================================================================
    // LEA用: セグメントなしのオフセット計算
    // ================================================================
    calcEAOffsetOnly(mod, rm) {
        let base = 0;
        switch (rm) {
            case 0:
                base = (this.reg.bx + this.reg.si) & 0xFFFF;
                break;
            case 1:
                base = (this.reg.bx + this.reg.di) & 0xFFFF;
                break;
            case 2:
                base = (this.reg.bp + this.reg.si) & 0xFFFF;
                break;
            case 3:
                base = (this.reg.bp + this.reg.di) & 0xFFFF;
                break;
            case 4:
                base = this.reg.si;
                break;
            case 5:
                base = this.reg.di;
                break;
            case 6:
                base = mod === 0 ? this.fetchWord() : this.reg.bp;
                break;
            case 7:
                base = this.reg.bx;
                break;
        }
        if (mod === 1)
            base = (base + this.fetchSByte()) & 0xFFFF;
        else if (mod === 2)
            base = (base + this.fetchSWord()) & 0xFFFF;
        return base & 0xFFFF;
    }
    // ================================================================
    // 符号変換ユーティリティ
    // ================================================================
    toSigned8(v) { return v >= 0x80 ? v - 0x100 : v; }
    toSigned16(v) { return v >= 0x8000 ? v - 0x10000 : v; }
    toSigned32(v) { return v >= 0x80000000 ? v - 0x100000000 : v; }
    // ================================================================
    // 実行
    // ================================================================
    run(maxSteps = 1000000) {
        for (let i = 0; i < maxSteps && !this.halted; i++) {
            this.step();
        }
    }
    // ステップ実行（1命令実行してログを返す）
    stepOne() {
        const cs = this.reg.cs;
        const ip = this.reg.ip;
        const opcode = this.mem.read8(this.reg.segmented(cs, ip));
        this.step();
        return { cs, ip, opcode };
    }
    // キーボード入力バッファに追加（IDE側から呼ぶ）
    pushKey(scancode, ascii) {
        this.biosKeyBuffer.push((scancode << 8) | ascii);
    }
    getBiosVideoState() {
        return {
            mode: this.biosVideoMode,
            isGraphics: this.biosVideoMode === 0x13,
            rows: this.biosVideoRows,
            cols: this.biosVideoCols,
            cursorRow: this.biosCursorRow,
            cursorCol: this.biosCursorCol,
            vramBase: this.VRAM_BASE,
        };
    }
    installBIOS() {
        // ── IVTセットアップ (0000:0000 - 0000:03FF) ──
        // 全256ベクタをダミーIRETに向ける (F000:FF00)
        const BIOS_SEG = 0xF000;
        const IRET_OFF = 0xFF00;
        for (let i = 0; i < 256; i++) {
            this.mem.write16(i * 4, IRET_OFF);
            this.mem.write16(i * 4 + 2, BIOS_SEG);
        }
        // ダミーIRET at F000:FF00
        this.mem.write8(this.reg.segmented(BIOS_SEG, IRET_OFF), 0xCF); // IRET
        // ── BIOS Data Area (0040:0000 = 0x00400) ──
        this.mem.write16(0x0400, 0x03F8); // COM1 base
        this.mem.write16(0x0410, 0x0021); // equipment word (80x25 color, 1 floppy)
        this.mem.write16(0x0413, 640); // conventional memory (KB)
        this.mem.write8(0x0449, 0x03); // current video mode
        this.mem.write16(0x044A, 80); // columns per row
        this.mem.write16(0x044C, 0x1000); // video page size
        this.mem.write16(0x0450, 0x0000); // cursor position page 0 (col,row)
        this.mem.write16(0x0463, 0x03D4); // CRT controller base
        this.mem.write8(0x0484, 24); // rows - 1
        this.mem.write16(0x0485, 16); // char height
        this.mem.write16(0x048A, 0); // keyboard buffer head
        this.mem.write16(0x048C, 0); // keyboard buffer tail
        // Timer tick counter at 0040:006C (= 0x046C)
        this.mem.write16(0x046C, 0);
        this.mem.write16(0x046E, 0);
        // ── VRAM初期化 (B800:0000) ──
        for (let i = 0; i < 80 * 25; i++) {
            this.mem.write16(this.VRAM_BASE + i * 2, 0x0720); // space, attribute 07 (white on black)
        }
        // ── BIOS割り込みハンドラ登録（JS側で処理） ──
        this.registerBiosHandlers();
        // ── スタック ──
        this.reg.ss = 0x0030;
        this.reg.sp = 0x0100;
        // ── 初期セグメント ──
        this.reg.ds = 0x0000;
        this.reg.es = 0x0000;
    }
    registerBiosHandlers() {
        // ── INT 10h: Video Services ──
        this.registerInterrupt(0x10, () => {
            switch (this.reg.ah) {
                case 0x00: // Set video mode
                    this.biosVideoMode = this.reg.al & 0x7F; // bit7=don't clear
                    this.biosCursorRow = 0;
                    this.biosCursorCol = 0;
                    if (this.biosVideoMode === 0x13) {
                        // Mode 13h: 320x200x256color, VRAM at 0xA0000
                        for (let i = 0; i < 320 * 200; i++) {
                            this.mem.write8(0xA0000 + i, 0);
                        }
                        if (this.onVideoModeChange) this.onVideoModeChange(0x13);
                    if (typeof window!=='undefined'&&window._onVideoModeChange) window._onVideoModeChange(0x13);
                    } else {
                        // Text mode: clear B8000
                        for (let i = 0; i < 80 * 25; i++) {
                            this.mem.write16(this.VRAM_BASE + i * 2, 0x0720);
                        }
                        if (this.onVideoModeChange) this.onVideoModeChange(this.biosVideoMode);
                        if (typeof window!=='undefined'&&window._onVideoModeChange) window._onVideoModeChange(this.biosVideoMode);
                    }
                    break;
                case 0x01: // Set cursor shape (stub)
                    break;
                case 0x02: // Set cursor position
                    this.biosCursorRow = this.reg.dh;
                    this.biosCursorCol = this.reg.dl;
                    this.mem.write8(0x0450, this.reg.dl);
                    this.mem.write8(0x0451, this.reg.dh);
                    break;
                case 0x03: // Get cursor position
                    this.reg.dh = this.biosCursorRow;
                    this.reg.dl = this.biosCursorCol;
                    this.reg.ch = 0x06; // cursor start
                    this.reg.cl = 0x07; // cursor end
                    break;
                case 0x05: // Set active page (stub)
                    break;
                case 0x06: { // Scroll up
                    const lines = this.reg.al || 25;
                    const attr = this.reg.bh;
                    const r1 = this.reg.ch, c1 = this.reg.cl, r2 = this.reg.dh, c2 = this.reg.dl;
                    for (let row = r1; row <= r2; row++) {
                        for (let col = c1; col <= c2; col++) {
                            const srcRow = row + lines;
                            if (srcRow <= r2) {
                                const src = this.VRAM_BASE + (srcRow * 80 + col) * 2;
                                const dst = this.VRAM_BASE + (row * 80 + col) * 2;
                                this.mem.write16(dst, this.mem.read16(src));
                            }
                            else {
                                const dst = this.VRAM_BASE + (row * 80 + col) * 2;
                                this.mem.write16(dst, (attr << 8) | 0x20);
                            }
                        }
                    }
                    break;
                }
                case 0x07: { // Scroll down
                    const lines = this.reg.al || 25;
                    const attr = this.reg.bh;
                    const r1 = this.reg.ch, c1 = this.reg.cl, r2 = this.reg.dh, c2 = this.reg.dl;
                    for (let row = r2; row >= r1; row--) {
                        for (let col = c1; col <= c2; col++) {
                            const srcRow = row - lines;
                            if (srcRow >= r1) {
                                const src = this.VRAM_BASE + (srcRow * 80 + col) * 2;
                                const dst = this.VRAM_BASE + (row * 80 + col) * 2;
                                this.mem.write16(dst, this.mem.read16(src));
                            }
                            else {
                                const dst = this.VRAM_BASE + (row * 80 + col) * 2;
                                this.mem.write16(dst, (attr << 8) | 0x20);
                            }
                        }
                    }
                    break;
                }
                case 0x08: { // Read char/attr at cursor
                    const addr = this.VRAM_BASE + (this.biosCursorRow * 80 + this.biosCursorCol) * 2;
                    this.reg.al = this.mem.read8(addr); // char
                    this.reg.ah = this.mem.read8(addr + 1); // attr
                    break;
                }
                case 0x09: { // Write char/attr at cursor
                    const ch = this.reg.al, attr = this.reg.bl, count = this.reg.cx;
                    let pos = this.biosCursorRow * 80 + this.biosCursorCol;
                    for (let i = 0; i < count && pos < 80 * 25; i++, pos++) {
                        this.mem.write16(this.VRAM_BASE + pos * 2, (attr << 8) | ch);
                    }
                    break;
                }
                case 0x0A: { // Write char at cursor (attr unchanged)
                    const ch = this.reg.al, count = this.reg.cx;
                    let pos = this.biosCursorRow * 80 + this.biosCursorCol;
                    for (let i = 0; i < count && pos < 80 * 25; i++, pos++) {
                        this.mem.write8(this.VRAM_BASE + pos * 2, ch);
                    }
                    break;
                }
                case 0x0E: { // Teletype output
                    const ch = this.reg.al;
                    if (ch === 0x07) { /* bell - ignore */ }
                    else if (ch === 0x08) { // backspace
                        if (this.biosCursorCol > 0)
                            this.biosCursorCol--;
                    }
                    else if (ch === 0x0A) { // line feed
                        this.biosCursorRow++;
                    }
                    else if (ch === 0x0D) { // carriage return
                        this.biosCursorCol = 0;
                    }
                    else {
                        const addr = this.VRAM_BASE + (this.biosCursorRow * 80 + this.biosCursorCol) * 2;
                        this.mem.write8(addr, ch);
                        this.mem.write8(addr + 1, 0x07); // default attr
                        this.biosCursorCol++;
                    }
                    if (this.biosCursorCol >= 80) {
                        this.biosCursorCol = 0;
                        this.biosCursorRow++;
                    }
                    if (this.biosCursorRow >= 25) {
                        // Scroll up 1 line
                        for (let i = 0; i < 80 * 24; i++) {
                            this.mem.write16(this.VRAM_BASE + i * 2, this.mem.read16(this.VRAM_BASE + (i + 80) * 2));
                        }
                        for (let i = 0; i < 80; i++) {
                            this.mem.write16(this.VRAM_BASE + (24 * 80 + i) * 2, 0x0720);
                        }
                        this.biosCursorRow = 24;
                    }
                    this.mem.write8(0x0450, this.biosCursorCol);
                    this.mem.write8(0x0451, this.biosCursorRow);
                    if (this.onBiosOutput)
                        this.onBiosOutput(String.fromCharCode(ch));
                    break;
                }
                case 0x0F: // Get video mode
                    this.reg.al = this.biosVideoMode;
                    this.reg.ah = this.biosVideoCols;
                    this.reg.bh = 0; // active page
                    break;
                case 0x10: // Palette (stub)
                    break;
                case 0x11: // Character generator
                    if (this.reg.al === 0x30) { // Get font info
                        this.reg.cx = this.biosCharHeight || 16;
                        this.reg.dl = this.biosVideoRows ? this.biosVideoRows - 1 : 24;
                    } else if (this.reg.al === 0x12 || this.reg.al === 0x11 || this.reg.al === 0x14) {
                        // 0x11 = Load 8x14 font, 0x12 = Load 8x8 font, 0x14 = Load 8x16 font
                        if (this.reg.al === 0x12) {
                            this.biosCharHeight = 8;
                            this.biosVideoRows = 50; // 400/8 = 50 rows (or 43 on EGA)
                        } else if (this.reg.al === 0x11) {
                            this.biosCharHeight = 14;
                            this.biosVideoRows = 28;
                        } else {
                            this.biosCharHeight = 16;
                            this.biosVideoRows = 25;
                        }
                        // Update BDA
                        this.mem.write8(0x0484, this.biosVideoRows - 1); // rows - 1
                        this.mem.write16(0x0485, this.biosCharHeight); // char height
                    }
                    break;
                case 0x12: // Alternate select (stub)
                    if (this.reg.bl === 0x10) { // Get EGA info
                        this.reg.bh = 0; // color
                        this.reg.bl = 3; // 256K memory
                        this.reg.cl = 0;
                        this.reg.ch = 0;
                    }
                    break;
                case 0x1A: // Display combination (VGA)
                    this.reg.al = 0x1A; // VGA
                    this.reg.bl = 0x08; // VGA + color analog
                    break;
            }
        });
        // ── INT 11h: Equipment determination ──
        this.registerInterrupt(0x11, () => {
            this.reg.ax = this.mem.read16(0x0410);
        });
        // ── INT 12h: Memory size ──
        this.registerInterrupt(0x12, () => {
            this.reg.ax = this.mem.read16(0x0413);
        });
        // ── INT 13h: Disk Services ──
        this.registerInterrupt(0x13, () => {
            switch (this.reg.ah) {
                case 0x00: // Reset disk
                    this.reg.ah = 0x00;
                    this.reg.setFlag(FLAGS.CF, false);
                    break;
                case 0x02: { // Read sectors
                    // 仮想ディスク: localStorage経由で読む
                    // DL=drive, DH=head, CH=cyl, CL=sector, AL=count, ES:BX=buffer
                    const drive = this.reg.dl;
                    const head = this.reg.dh;
                    const cyl = this.reg.ch | ((this.reg.cl & 0xC0) << 2);
                    const sector = this.reg.cl & 0x3F;
                    const count = this.reg.al;
                    const bufAddr = this.reg.segmented(this.reg.es, this.reg.bx);
                    // CHS→LBA: LBA = (C * heads + H) * sectors + (S - 1)
                    // 仮想ディスク: 2 heads, 18 sectors/track
                    const lba = (cyl * 2 + head) * 18 + (sector - 1);
                    // ディスクイメージハンドラが設定されてる場合
                    if (this.diskReadHandler) {
                        const ok = this.diskReadHandler(drive, lba, count, bufAddr);
                        this.reg.ah = ok ? 0x00 : 0x04; // 0=success, 4=sector not found
                        this.reg.setFlag(FLAGS.CF, !ok);
                        if (ok)
                            this.reg.al = count;
                    }
                    else {
                        this.reg.ah = 0x80; // timeout / not ready
                        this.reg.setFlag(FLAGS.CF, true);
                    }
                    break;
                }
                case 0x08: { // Get drive parameters
                    const drive = this.reg.dl;
                    if (drive === 0x00) { // floppy A:
                        this.reg.ah = 0;
                        this.reg.bl = 4; // type: 1.44M
                        this.reg.ch = 79; // max cyl
                        this.reg.cl = 18; // max sectors
                        this.reg.dh = 1; // max heads
                        this.reg.dl = 1; // number of drives
                        this.reg.setFlag(FLAGS.CF, false);
                    }
                    else if (drive === 0x80) { // HDD
                        this.reg.ah = 0;
                        this.reg.ch = 0;
                        this.reg.cl = 0;
                        this.reg.dh = 0;
                        this.reg.dl = 0; // no HDD
                        this.reg.setFlag(FLAGS.CF, true); // no HDD
                    }
                    else {
                        this.reg.ah = 0x01;
                        this.reg.setFlag(FLAGS.CF, true);
                    }
                    break;
                }
                case 0x15: // Get disk type
                    this.reg.ah = 0x01; // floppy without change detection
                    this.reg.setFlag(FLAGS.CF, false);
                    break;
                default:
                    this.reg.ah = 0x01; // invalid command
                    this.reg.setFlag(FLAGS.CF, true);
            }
        });
        // ── INT 14h: Serial port (stub) ──
        this.registerInterrupt(0x14, () => {
            this.reg.ah = 0x80; // timeout
        });
        // ── INT 15h: System services ──
        this.registerInterrupt(0x15, () => {
            switch (this.reg.ah) {
                case 0x88: // Extended memory size
                    this.reg.ax = 0; // no extended memory
                    this.reg.setFlag(FLAGS.CF, false);
                    break;
                case 0xC0: // Get system configuration
                    this.reg.ah = 0x86; // not supported
                    this.reg.setFlag(FLAGS.CF, true);
                    break;
                case 0x41: // Wait on external event (stub)
                    break;
                case 0x86: { // Wait (microseconds in CX:DX)
                    const us = (this.reg.cx << 16) | this.reg.dx;
                    // Convert to CPU cycles at 4.77MHz: ~4.77 cycles per microsecond
                    this.waitCycles = Math.round(us * 4.77);
                    this.reg.setFlag(FLAGS.CF, false);
                    break;
                }
                case 0x24: // A20 gate (stub - always enabled)
                    this.reg.ah = 0;
                    this.reg.setFlag(FLAGS.CF, false);
                    break;
                default:
                    this.reg.setFlag(FLAGS.CF, true);
            }
        });
        // ── INT 16h: Keyboard Services ──
        this.registerInterrupt(0x16, () => {
            switch (this.reg.ah) {
                case 0x00: // Wait for key
                case 0x10: // Wait for key (extended)
                    if (this.biosKeyBuffer.length > 0) {
                        const key = this.biosKeyBuffer.shift();
                        this.reg.ah = (key >> 8) & 0xFF; // scan code
                        this.reg.al = key & 0xFF; // ASCII
                    }
                    else {
                        // キーがない場合、ビジーウェイト回避でhalt
                        this.reg.ip = (this.reg.ip - 2) & 0xFFFF; // INT 16hを再実行するようIPを戻す
                        this.halted = true; // 一時停止（キー入力で再開）
                        this.haltReason = 'key_wait';
                    }
                    break;
                case 0x01: // Check key available
                case 0x11: // Check key available (extended)
                    if (this.biosKeyBuffer.length > 0) {
                        const key = this.biosKeyBuffer[0];
                        this.reg.ah = (key >> 8) & 0xFF;
                        this.reg.al = key & 0xFF;
                        this.reg.setFlag(FLAGS.ZF, false); // key available
                    }
                    else {
                        this.reg.setFlag(FLAGS.ZF, true); // no key
                    }
                    break;
                case 0x02: // Get shift key status
                    this.reg.al = 0; // no shift keys
                    break;
            }
        });
        // ── INT 17h: Printer (stub) ──
        this.registerInterrupt(0x17, () => {
            this.reg.ah = 0x30; // not available
        });
        // ── INT 19h: Bootstrap loader ──
        this.registerInterrupt(0x19, () => {
            // ブートセクタ読み込み: 0000:7C00
            this.reg.dl = 0x00; // floppy A:
            this.reg.ah = 0x02; // read sectors
            this.reg.al = 0x01; // 1 sector
            this.reg.ch = 0x00; // cyl 0
            this.reg.cl = 0x01; // sector 1
            this.reg.dh = 0x00; // head 0
            this.reg.es = 0x0000;
            this.reg.bx = 0x7C00;
            this.doInterrupt(0x13);
            // ブートセクタにジャンプ
            if (!this.reg.getFlag(FLAGS.CF)) {
                this.reg.cs = 0x0000;
                this.reg.ip = 0x7C00;
                this.reg.dl = 0x00; // boot drive
            }
        });
        // ── INT 1Ah: Time Services ──
        this.registerInterrupt(0x1A, () => {
            switch (this.reg.ah) {
                case 0x00: { // Get tick count
                    const now = Date.now();
                    const ticks = Math.floor((now % 86400000) * 18.2065 / 1000);
                    this.reg.cx = (ticks >> 16) & 0xFFFF;
                    this.reg.dx = ticks & 0xFFFF;
                    this.reg.al = 0; // midnight flag
                    break;
                }
                case 0x01: // Set tick count (stub)
                    break;
                case 0x02: { // Get RTC time
                    const d = new Date();
                    const toBCD = (n) => ((n / 10 | 0) << 4) | (n % 10);
                    this.reg.ch = toBCD(d.getHours());
                    this.reg.cl = toBCD(d.getMinutes());
                    this.reg.dh = toBCD(d.getSeconds());
                    this.reg.dl = 0;
                    this.reg.setFlag(FLAGS.CF, false);
                    break;
                }
                case 0x04: { // Get RTC date
                    const d = new Date();
                    const toBCD = (n) => ((n / 10 | 0) << 4) | (n % 10);
                    this.reg.ch = toBCD(d.getFullYear() / 100 | 0);
                    this.reg.cl = toBCD(d.getFullYear() % 100);
                    this.reg.dh = toBCD(d.getMonth() + 1);
                    this.reg.dl = toBCD(d.getDate());
                    this.reg.setFlag(FLAGS.CF, false);
                    break;
                }
            }
        });
        // ── INT 20h: Program Terminate (old style) ──
        this.registerInterrupt(0x20, () => {
            this.halted = true;
            this.haltReason = 'program_exit';
        });
        // ── INT 21h: DOS Services (最低限) ──
        this.registerInterrupt(0x21, () => {
            var _a, _b, _c, _d, _e;
            switch (this.reg.ah) {
                case 0x01: { // Read char with echo
                    if (this.biosKeyBuffer.length > 0) {
                        const key = this.biosKeyBuffer.shift();
                        const ch = key & 0xFF;
                        // echo via INT 10h/0Eh
                        const saveAX = this.reg.ax;
                        this.reg.ah = 0x0E;
                        this.reg.al = ch;
                        (_a = this.interruptHandlers.get(0x10)) === null || _a === void 0 ? void 0 : _a();
                        this.reg.ax = saveAX;
                        this.reg.al = ch; // return char in AL
                    }
                    else {
                        this.reg.ip = (this.reg.ip - 2) & 0xFFFF;
                        this.halted = true;
                        this.haltReason = 'key_wait';
                    }
                    break;
                }
                case 0x02: { // Display char
                    const ch = this.reg.dl;
                    const oldAX = this.reg.ax;
                    this.reg.ah = 0x0E;
                    this.reg.al = ch;
                    (_b = this.interruptHandlers.get(0x10)) === null || _b === void 0 ? void 0 : _b();
                    this.reg.ax = oldAX;
                    break;
                }
                case 0x06: { // Direct console I/O
                    if (this.reg.dl === 0xFF) { // input
                        if (this.biosKeyBuffer.length > 0) {
                            this.reg.al = this.biosKeyBuffer.shift() & 0xFF;
                            this.reg.setFlag(FLAGS.ZF, false);
                        }
                        else {
                            this.reg.al = 0;
                            this.reg.setFlag(FLAGS.ZF, true);
                        }
                    }
                    else { // output
                        const oldAX = this.reg.ax;
                        this.reg.ah = 0x0E;
                        this.reg.al = this.reg.dl;
                        (_c = this.interruptHandlers.get(0x10)) === null || _c === void 0 ? void 0 : _c();
                        this.reg.ax = oldAX;
                    }
                    break;
                }
                case 0x07: // Direct char input (no echo)
                case 0x08: { // Char input (no echo)
                    if (this.biosKeyBuffer.length > 0) {
                        this.reg.al = this.biosKeyBuffer.shift() & 0xFF;
                    }
                    else {
                        this.reg.ip = (this.reg.ip - 2) & 0xFFFF;
                        this.halted = true;
                        this.haltReason = 'key_wait';
                    }
                    break;
                }
                case 0x09: { // Print string (terminated by '$')
                    let addr = this.reg.segmented(this.reg.ds, this.reg.dx);
                    let lim = 0;
                    while (lim++ < 65536) {
                        const ch = this.mem.read8(addr++);
                        if (ch === 0x24)
                            break; // '$'
                        const oldAX = this.reg.ax;
                        this.reg.ah = 0x0E;
                        this.reg.al = ch;
                        (_d = this.interruptHandlers.get(0x10)) === null || _d === void 0 ? void 0 : _d();
                        this.reg.ax = oldAX;
                    }
                    this.reg.al = 0x24;
                    break;
                }
                case 0x0A: { // Buffered input
                    const bufAddr = this.reg.segmented(this.reg.ds, this.reg.dx);
                    const maxLen = this.mem.read8(bufAddr);
                    // 簡略版: キーバッファから読む
                    let count = 0;
                    const chars = [];
                    while (count < maxLen) {
                        if (this.biosKeyBuffer.length === 0)
                            break;
                        const key = this.biosKeyBuffer.shift() & 0xFF;
                        if (key === 0x0D)
                            break;
                        chars.push(key);
                        count++;
                    }
                    this.mem.write8(bufAddr + 1, count);
                    for (let i = 0; i < count; i++) {
                        this.mem.write8(bufAddr + 2 + i, chars[i]);
                    }
                    this.mem.write8(bufAddr + 2 + count, 0x0D);
                    break;
                }
                case 0x0B: // Check stdin status
                    this.reg.al = this.biosKeyBuffer.length > 0 ? 0xFF : 0x00;
                    break;
                case 0x25: { // Set interrupt vector
                    const vec = this.reg.al;
                    this.mem.write16(vec * 4, this.reg.dx);
                    this.mem.write16(vec * 4 + 2, this.reg.ds);
                    break;
                }
                case 0x2A: { // Get date
                    const d = new Date();
                    this.reg.cx = d.getFullYear();
                    this.reg.dh = d.getMonth() + 1;
                    this.reg.dl = d.getDate();
                    this.reg.al = d.getDay();
                    break;
                }
                case 0x2C: { // Get time
                    const d = new Date();
                    this.reg.ch = d.getHours();
                    this.reg.cl = d.getMinutes();
                    this.reg.dh = d.getSeconds();
                    this.reg.dl = Math.floor(d.getMilliseconds() / 10);
                    break;
                }
                case 0x30: // Get DOS version
                    this.reg.al = 5; // major (DOS 5.0)
                    this.reg.ah = 0; // minor
                    this.reg.bh = 0xFF; // OEM: IBM
                    break;
                case 0x35: { // Get interrupt vector
                    const vec = this.reg.al;
                    this.reg.bx = this.mem.read16(vec * 4);
                    this.reg.es = this.mem.read16(vec * 4 + 2);
                    break;
                }
                case 0x40: { // Write to file handle
                    // handle: BX, count: CX, buffer: DS:DX
                    const handle = this.reg.bx;
                    if (handle === 1 || handle === 2) { // stdout / stderr
                        let addr = this.reg.segmented(this.reg.ds, this.reg.dx);
                        for (let i = 0; i < this.reg.cx; i++) {
                            const ch = this.mem.read8(addr++);
                            const oldAX = this.reg.ax;
                            this.reg.ah = 0x0E;
                            this.reg.al = ch;
                            (_e = this.interruptHandlers.get(0x10)) === null || _e === void 0 ? void 0 : _e();
                            this.reg.ax = oldAX;
                        }
                        this.reg.ax = this.reg.cx;
                        this.reg.setFlag(FLAGS.CF, false);
                    }
                    else {
                        this.reg.ax = 6; // invalid handle
                        this.reg.setFlag(FLAGS.CF, true);
                    }
                    break;
                }
                case 0x19: // Get current default drive
                    this.reg.al = 0; // A:
                    break;
                case 0x1A: { // Set DTA address
                    if (this.dosFileIO) this.dosFileIO.dtaSeg = this.reg.ds;
                    if (this.dosFileIO) this.dosFileIO.dtaOff = this.reg.dx;
                    break;
                }
                case 0x2F: // Get DTA address
                    if (this.dosFileIO) {
                        this.reg.es = this.dosFileIO.dtaSeg;
                        this.reg.bx = this.dosFileIO.dtaOff;
                    } else {
                        this.reg.es = 0;
                        this.reg.bx = 0x0080;
                    }
                    break;
                case 0x3C: // Create file (AH=3Ch, CX=attr, DS:DX=filename) → AX=handle
                case 0x3D: // Open file (AH=3Dh, AL=mode, DS:DX=filename) → AX=handle
                case 0x3E: // Close file (AH=3Eh, BX=handle)
                case 0x3F: // Read file (AH=3Fh, BX=handle, CX=count, DS:DX=buf) → AX=bytes read
                case 0x40: { // Write file (AH=40h, BX=handle, CX=count, DS:DX=buf) → AX=bytes written
                    if (this.dosFileIO) {
                        this.dosFileIO.handleFileIO(this);
                    } else {
                        // fallback for write to stdout/stderr
                        if (this.reg.ah === 0x40 && (this.reg.bx === 1 || this.reg.bx === 2)) {
                            let addr = this.reg.segmented(this.reg.ds, this.reg.dx);
                            for (let i = 0; i < this.reg.cx; i++) {
                                const ch = this.mem.read8(addr++);
                                const oldAX = this.reg.ax;
                                this.reg.ah = 0x0E;
                                this.reg.al = ch;
                                (_e = this.interruptHandlers.get(0x10)) === null || _e === void 0 ? void 0 : _e();
                                this.reg.ax = oldAX;
                            }
                            this.reg.ax = this.reg.cx;
                            this.reg.setFlag(FLAGS.CF, false);
                        } else {
                            this.reg.ax = 6; // invalid handle
                            this.reg.setFlag(FLAGS.CF, true);
                        }
                    }
                    break;
                }
                case 0x41: // Delete file (DS:DX=filename)
                case 0x42: // Seek (BX=handle, CX:DX=offset, AL=origin) → DX:AX=new pos
                case 0x43: // Get/Set file attributes
                case 0x47: // Get current directory
                case 0x4E: // FindFirst (CX=attr, DS:DX=spec)
                case 0x4F: // FindNext
                case 0x56: // Rename file
                case 0x57: // Get/Set file date/time
                case 0x3B: // Change directory
                {
                    if (this.dosFileIO) {
                        this.dosFileIO.handleFileIO(this);
                    } else {
                        this.reg.ax = 2; // file not found
                        this.reg.setFlag(FLAGS.CF, true);
                    }
                    break;
                }
                case 0x44: // IOCTL
                    if (this.reg.al === 0x00 && (this.reg.bx <= 2)) {
                        // Get device info for stdin/stdout/stderr
                        this.reg.dx = 0x80D3; // character device, stdin/stdout
                        this.reg.setFlag(FLAGS.CF, false);
                    } else if (this.reg.al === 0x07) {
                        // Get output status
                        this.reg.al = 0xFF; // ready
                        this.reg.setFlag(FLAGS.CF, false);
                    } else {
                        this.reg.ax = 1;
                        this.reg.setFlag(FLAGS.CF, true);
                    }
                    break;
                case 0x48: // Allocate memory (BX=paragraphs)
                case 0x49: // Free memory (ES=segment)
                case 0x4A: // Resize memory (ES=segment, BX=new size)
                {
                    if (this.dosFileIO) {
                        this.dosFileIO.handleMemory(this);
                    } else {
                        if (this.reg.ah === 0x4A) {
                            this.reg.setFlag(FLAGS.CF, false);
                        } else {
                            this.reg.ax = 8;
                            this.reg.bx = 0;
                            this.reg.setFlag(FLAGS.CF, true);
                        }
                    }
                    break;
                }
                case 0x4B: // EXEC (load and execute program)
                    // Stub - not supported in this environment
                    this.reg.ax = 2; // file not found
                    this.reg.setFlag(FLAGS.CF, true);
                    break;
                case 0x4C: // Terminate program
                    this.halted = true;
                    this.haltReason = 'program_exit';
                    break;
                case 0x4D: // Get return code
                    this.reg.ax = 0; // normal termination, code 0
                    break;
                case 0x50: // Set current PSP
                    if (this.dosFileIO) this.dosFileIO.currentPSP = this.reg.bx;
                    break;
                case 0x51: // Get current PSP
                case 0x62: // Get PSP address
                    this.reg.bx = this.dosFileIO ? this.dosFileIO.currentPSP : 0;
                    break;
                case 0x59: // Get extended error info
                    this.reg.ax = 0; // no error
                    this.reg.bh = 0; this.reg.bl = 0; this.reg.ch = 0;
                    break;
                default:
                    // Unknown DOS function - ignore
                    break;
            }
        });
        // ── INT 22h: Terminate address (stub) ──
        this.registerInterrupt(0x22, () => {});
        // ── INT 23h: Ctrl-C handler (stub) ──
        this.registerInterrupt(0x23, () => {});
        // ── INT 24h: Critical error handler (stub) ──
        this.registerInterrupt(0x24, () => {
            this.reg.al = 0; // ignore error
        });
        // ── INT 27h: TSR (stub - just halt) ──
        this.registerInterrupt(0x27, () => {
            this.halted = true;
            this.haltReason = 'program_exit';
        });
        // ── INT 28h: DOS idle (stub) ──
        this.registerInterrupt(0x28, () => {});
        // ── INT 2Fh: Multiplex interrupt (stub) ──
        this.registerInterrupt(0x2F, () => {
            switch (this.reg.ah) {
                case 0x16: // Windows enhanced mode
                    if (this.reg.al === 0x00) this.reg.al = 0x00; // not running
                    break;
                case 0x43: // XMS
                    if (this.reg.al === 0x00) this.reg.al = 0x00; // not installed
                    break;
                default:
                    break;
            }
        });
        // ── INT 33h: Mouse Services (stub) ──
        this.registerInterrupt(0x33, () => {
            switch (this.reg.ax) {
                case 0x0000: // Reset/detect mouse
                    this.reg.ax = 0xFFFF; // mouse installed
                    this.reg.bx = 2; // 2 buttons
                    break;
                case 0x0001: // Show cursor
                    break;
                case 0x0002: // Hide cursor
                    break;
                case 0x0003: // Get position and button status
                    this.reg.bx = this.mouseButtons || 0;
                    this.reg.cx = this.mouseX || 0;
                    this.reg.dx = this.mouseY || 0;
                    break;
                case 0x0004: // Set position
                    this.mouseX = this.reg.cx;
                    this.mouseY = this.reg.dx;
                    break;
                case 0x0007: // Set horizontal range
                    break;
                case 0x0008: // Set vertical range
                    break;
                case 0x000B: // Get motion counters
                    this.reg.cx = 0;
                    this.reg.dx = 0;
                    break;
                case 0x000C: // Set user-defined handler
                    break;
                case 0x0015: // Get driver info
                    this.reg.bx = 8; // major
                    this.reg.cx = 0; // minor
                    break;
                case 0x001A: // Set mouse sensitivity
                    break;
                default:
                    break;
            }
        });
    }
    // ================================================================
    // デバッグ: レジスタダンプ
    // ================================================================
    dumpRegisters() {
        const r = this.reg;
        const f = (bit, name) => r.getFlag(bit) ? name : name.toLowerCase();
        return [
            `AX=${r.ax.toString(16).padStart(4, '0')} BX=${r.bx.toString(16).padStart(4, '0')} CX=${r.cx.toString(16).padStart(4, '0')} DX=${r.dx.toString(16).padStart(4, '0')}`,
            `SI=${r.si.toString(16).padStart(4, '0')} DI=${r.di.toString(16).padStart(4, '0')} SP=${r.sp.toString(16).padStart(4, '0')} BP=${r.bp.toString(16).padStart(4, '0')}`,
            `CS=${r.cs.toString(16).padStart(4, '0')} DS=${r.ds.toString(16).padStart(4, '0')} ES=${r.es.toString(16).padStart(4, '0')} SS=${r.ss.toString(16).padStart(4, '0')}`,
            `IP=${r.ip.toString(16).padStart(4, '0')} FLAGS=${r.flags.toString(16).padStart(4, '0')} [${f(FLAGS.OF, 'O')}${f(FLAGS.DF, 'D')}${f(FLAGS.IF, 'I')}${f(FLAGS.SF, 'S')}${f(FLAGS.ZF, 'Z')}${f(FLAGS.AF, 'A')}${f(FLAGS.PF, 'P')}${f(FLAGS.CF, 'C')}]`,
            `FS=${r.fs.toString(16).padStart(4, '0')} GS=${r.gs.toString(16).padStart(4, '0')}`,
            `Halted: ${this.halted}`,
        ].join('\n');
    }
    // BIOSタイマーティック更新 (0040:006C)
    tickBiosTimer() {
        const lo = this.mem.read16(0x046C);
        const hi = this.mem.read16(0x046E);
        const val = (hi * 0x10000 + lo + 1) & 0xFFFFFFFF;
        this.mem.write16(0x046C, val & 0xFFFF);
        this.mem.write16(0x046E, (val >>> 16) & 0xFFFF);
    }
}
function selfTest() {
    const groups = [];
    let totalPass = 0, totalFail = 0;
    function group(name, fn) {
        const tests = [];
        fn((tname, code, check, detail) => {
            const m = new Memory();
            const c = new CPU8086(m);
            // --- INT 10h のハンドラを修正 ---
            c.registerInterrupt(0x10, () => {
                if (c.reg.ah === 0x0E) {
                    // 文字出力（テスト環境ではログのみ）
                    if (typeof window !== 'undefined' && typeof window.log === 'function') {
                        window.log(String.fromCharCode(c.reg.al), 'info');
                    }
                }
            });
            c.registerInterrupt(0x21, () => {
                if (c.reg.ah === 0x4C) {
                    c.halted = true;
                    c.haltReason = 'program_exit';
                }
            });
            // --- ここまで ---
            c.reg.cs = 0;
            c.reg.ip = 0;
            c.reg.ds = 0;
            c.reg.es = 0;
            c.reg.ss = 0;
            c.reg.sp = 0xFFFE;
            m.load(0, code);
            try {
                c.run(100000);
                const ok = check(c, m);
                tests.push({ name: tname, pass: ok, detail: ok ? undefined : (detail || 'check failed') });
                if (ok)
                    totalPass++;
                else
                    totalFail++;
            }
            catch (e) {
                tests.push({ name: tname, pass: false, detail: 'ERROR: ' + e.message });
                totalFail++;
            }
        });
        let p = 0, f = 0;
        tests.forEach(t => { if (t.pass)
            p++;
        else
            f++; });
        groups.push({ group: name, tests, passCount: p, failCount: f });
    }
    // ── helper ──
    const HLT = 0xF4;
    const CF = FLAGS.CF, ZF = FLAGS.ZF, SF = FLAGS.SF, OF = FLAGS.OF, PF = FLAGS.PF, AF = FLAGS.AF, DF = FLAGS.DF;
    // ================================================================
    // MOV 命令
    // ================================================================
    group('MOV', t => {
        t('MOV AX,imm16', [0xB8, 0x34, 0x12, HLT], c => c.reg.ax === 0x1234);
        t('MOV BX,imm16', [0xBB, 0xCD, 0xAB, HLT], c => c.reg.bx === 0xABCD);
        t('MOV CX,imm16', [0xB9, 0xFF, 0x00, HLT], c => c.reg.cx === 0x00FF);
        t('MOV DX,imm16', [0xBA, 0x00, 0x80, HLT], c => c.reg.dx === 0x8000);
        t('MOV AL,imm8', [0xB0, 0x42, HLT], c => c.reg.al === 0x42);
        t('MOV AH,imm8', [0xB4, 0x0E, HLT], c => c.reg.ah === 0x0E);
        t('MOV BL,imm8', [0xB3, 0xFF, HLT], c => c.reg.bl === 0xFF);
        t('MOV r16,r16 (AX←BX)', [0xBB, 0x34, 0x12, 0x89, 0xD8, HLT], c => c.reg.ax === 0x1234);
        t('MOV r8,r8 (AL←BL)', [0xB3, 0x42, 0x88, 0xD8, HLT], c => c.reg.al === 0x42);
        // MOV [mem],r16 → MOV r16,[mem]
        t('MOV [BX+02],AX / MOV CX,[BX+02]', [
            0xBB, 0x00, 0x01, 0xB8, 0xEF, 0xBE, // BX=0x100, AX=0xBEEF
            0x89, 0x47, 0x02, // MOV [BX+02], AX
            0x8B, 0x4F, 0x02, // MOV CX, [BX+02]
            HLT
        ], c => c.reg.cx === 0xBEEF);
        t('MOV [imm16],AL / MOV BL,[imm16]', [
            0xB0, 0x55, // MOV AL, 0x55
            0xA2, 0x00, 0x02, // MOV [0x200], AL
            0x8A, 0x1E, 0x00, 0x02, // MOV BL, [0x200]
            HLT
        ], c => c.reg.bl === 0x55);
        // MOV sreg
        t('MOV DS,AX', [0xB8, 0x00, 0x10, 0x8E, 0xD8, HLT], c => c.reg.ds === 0x1000);
        t('MOV AX,ES', [0x8C, 0xC0, HLT], c => c.reg.ax === 0);
        // MOV r/m16,imm16
        t('MOV WORD [0x200],1234h', [0xC7, 0x06, 0x00, 0x02, 0x34, 0x12, HLT], (c, m) => m.read16(0x200) === 0x1234);
        t('MOV BYTE [0x200],42h', [0xC6, 0x06, 0x00, 0x02, 0x42, HLT], (c, m) => m.read8(0x200) === 0x42);
    });
    // ================================================================
    // ADD / ADC
    // ================================================================
    group('ADD/ADC', t => {
        t('ADD AX,imm16', [0xB8, 0x34, 0x12, 0x05, 0x78, 0x56, HLT], c => c.reg.ax === 0x68AC);
        t('ADD AL,imm8', [0xB0, 0x10, 0x04, 0x20, HLT], c => c.reg.al === 0x30);
        t('ADD r16,r16', [0xB8, 0xFF, 0x00, 0xBB, 0x01, 0x00, 0x01, 0xD8, HLT], c => c.reg.ax === 0x0100);
        t('ADD CF set', [0xB0, 0xFF, 0x04, 0x02, HLT], c => c.reg.al === 0x01 && c.reg.getFlag(CF));
        t('ADD ZF set', [0xB0, 0x01, 0x04, 0xFF, HLT], c => c.reg.al === 0 && c.reg.getFlag(ZF));
        t('ADD OF set', [0xB8, 0xFF, 0x7F, 0x05, 0x01, 0x00, HLT], c => c.reg.ax === 0x8000 && c.reg.getFlag(OF));
        t('ADD [BX+02],imm8', [0xBB, 0x00, 0x01, 0xC6, 0x47, 0x02, 0x0A, 0x80, 0x47, 0x02, 0x05, HLT], (c, m) => m.read8(0x0102) === 0x0F);
        // ADC
        t('ADC AX,0 (CF=1)', [0xF9, 0xB8, 0x05, 0x00, 0x15, 0x00, 0x00, HLT], c => c.reg.ax === 6);
        t('ADC r8+CF', [0xF9, 0xB0, 0xFE, 0x14, 0x01, HLT], c => c.reg.al === 0x00 && c.reg.getFlag(CF));
    });
    // ================================================================
    // SUB / SBB / CMP
    // ================================================================
    group('SUB/SBB/CMP', t => {
        t('SUB AX,imm16', [0xB8, 0x00, 0x10, 0x2D, 0x01, 0x00, HLT], c => c.reg.ax === 0x0FFF);
        t('SUB AL,imm8 → negative', [0xB0, 0x01, 0x2C, 0x02, HLT], c => c.reg.al === 0xFF && c.reg.getFlag(SF) && c.reg.getFlag(CF));
        t('SUB → ZF', [0xB8, 0x42, 0x00, 0x2D, 0x42, 0x00, HLT], c => c.reg.ax === 0 && c.reg.getFlag(ZF));
        // SBB
        t('SBB AX,0 (CF=1)', [0xF9, 0xB8, 0x05, 0x00, 0x1D, 0x00, 0x00, HLT], c => c.reg.ax === 4);
        // CMP (no writeback)
        t('CMP AX,AX → ZF, val unchanged', [0xB8, 0x42, 0x00, 0x3D, 0x42, 0x00, HLT], c => c.reg.ax === 0x42 && c.reg.getFlag(ZF));
        t('CMP AX,imm > → CF', [0xB8, 0x01, 0x00, 0x3D, 0x02, 0x00, HLT], c => c.reg.ax === 1 && c.reg.getFlag(CF));
        t('CMP r8,r8', [0xB0, 0x05, 0xB1, 0x05, 0x38, 0xC8, HLT], c => c.reg.getFlag(ZF));
    });
    // ================================================================
    // INC / DEC
    // ================================================================
    group('INC/DEC', t => {
        t('INC AX', [0xB8, 0xFF, 0x00, 0x40, HLT], c => c.reg.ax === 0x0100);
        t('INC AX → ZF from 0xFFFF', [0xB8, 0xFF, 0xFF, 0x40, HLT], c => c.reg.ax === 0 && c.reg.getFlag(ZF));
        t('INC preserves CF', [0xF9, 0xB8, 0x00, 0x00, 0x40, HLT], c => c.reg.ax === 1 && c.reg.getFlag(CF));
        t('DEC AX', [0xB8, 0x01, 0x00, 0x48, HLT], c => c.reg.ax === 0 && c.reg.getFlag(ZF));
        t('DEC AX 0→0xFFFF', [0xB8, 0x00, 0x00, 0x48, HLT], c => c.reg.ax === 0xFFFF && c.reg.getFlag(SF));
        t('DEC preserves CF', [0xF9, 0xB8, 0x05, 0x00, 0x48, HLT], c => c.reg.ax === 4 && c.reg.getFlag(CF));
        t('INC r/m8', [0xB3, 0x41, 0xFE, 0xC3, HLT], c => c.reg.bl === 0x42);
        t('DEC r/m8', [0xB3, 0x01, 0xFE, 0xCB, HLT], c => c.reg.bl === 0 && c.reg.getFlag(ZF));
        t('INC WORD [BX+04]', [0xBB, 0x00, 0x01, 0xC7, 0x47, 0x04, 0xFF, 0x00, 0xFF, 0x47, 0x04, HLT], (c, m) => m.read16(0x0104) === 0x0100);
    });
    // ================================================================
    // AND / OR / XOR / NOT / NEG / TEST
    // ================================================================
    group('Logic', t => {
        t('AND AX,imm16', [0xB8, 0xFF, 0x0F, 0x25, 0x0F, 0x00, HLT], c => c.reg.ax === 0x000F && !c.reg.getFlag(CF) && !c.reg.getFlag(OF));
        t('OR AX,imm16', [0xB8, 0x0F, 0x00, 0x0D, 0xF0, 0x00, HLT], c => c.reg.ax === 0x00FF);
        t('XOR AX,AX → 0', [0xB8, 0x42, 0x00, 0x31, 0xC0, HLT], c => c.reg.ax === 0 && c.reg.getFlag(ZF));
        t('NOT AX', [0xB8, 0x00, 0xFF, 0xF7, 0xD0, HLT], c => c.reg.ax === 0x00FF);
        t('NOT AL', [0xB0, 0xAA, 0xF6, 0xD0, HLT], c => c.reg.al === 0x55);
        t('NEG AX', [0xB8, 0x05, 0x00, 0xF7, 0xD8, HLT], c => c.reg.ax === 0xFFFB && c.reg.getFlag(CF));
        t('NEG 0 → CF=0', [0xB8, 0x00, 0x00, 0xF7, 0xD8, HLT], c => c.reg.ax === 0 && !c.reg.getFlag(CF));
        t('TEST AL,imm8 → ZF', [0xB0, 0xF0, 0xA8, 0x0F, HLT], c => c.reg.getFlag(ZF) && c.reg.al === 0xF0);
        t('TEST AX,imm16', [0xB8, 0x0F, 0x00, 0xA9, 0x0F, 0x00, HLT], c => !c.reg.getFlag(ZF));
        t('OR [BX+02],AL', [0xBB, 0x00, 0x01, 0xB0, 0xF0, 0xC6, 0x47, 0x02, 0x0A, 0x08, 0x47, 0x02, HLT], (c, m) => m.read8(0x0102) === 0xFA);
    });
    // ================================================================
    // MUL / IMUL / DIV / IDIV
    // ================================================================
    group('MUL/DIV', t => {
        t('MUL r8 (AL*BL)', [0xB0, 0x0A, 0xB3, 0x05, 0xF6, 0xE3, HLT], c => c.reg.ax === 50);
        t('MUL r16 (AX*BX)', [0xB8, 0x00, 0x01, 0xBB, 0x10, 0x00, 0xF7, 0xE3, HLT], c => c.reg.ax === 0x1000 && c.reg.dx === 0);
        t('MUL overflow', [0xB8, 0x00, 0x80, 0xBB, 0x02, 0x00, 0xF7, 0xE3, HLT], c => c.reg.dx === 1 && c.reg.ax === 0 && c.reg.getFlag(CF));
        t('IMUL r8 (signed)', [0xB0, 0xFE, 0xB3, 0x02, 0xF6, 0xEB, HLT], c => c.reg.ax === ((-4) & 0xFFFF));
        t('DIV r8', [0xB8, 0x64, 0x00, 0xB3, 0x0A, 0xF6, 0xF3, HLT], c => c.reg.al === 10 && c.reg.ah === 0);
        t('DIV r16', [0xBA, 0x00, 0x00, 0xB8, 0xE8, 0x03, 0xBB, 0x64, 0x00, 0xF7, 0xF3, HLT], c => c.reg.ax === 10 && c.reg.dx === 0);
        t('IDIV r8 (signed)', [0xB8, 0xFB, 0xFF, 0xB3, 0x02, 0xF6, 0xFB, HLT], c => (c.reg.al & 0xFF) === ((-2) & 0xFF));
    });
    // ================================================================
    // シフト・ローテート
    // ================================================================
    group('Shift/Rotate', t => {
        t('SHL AX,1', [0xB8, 0x01, 0x00, 0xD1, 0xE0, HLT], c => c.reg.ax === 2);
        t('SHL AX,CL', [0xB8, 0x01, 0x00, 0xB1, 0x04, 0xD3, 0xE0, HLT], c => c.reg.ax === 0x10);
        t('SHR AX,1', [0xB8, 0x80, 0x00, 0xD1, 0xE8, HLT], c => c.reg.ax === 0x40);
        t('SAR AX,1 (sign extend)', [0xB8, 0x00, 0x80, 0xD1, 0xF8, HLT], c => c.reg.ax === 0xC000);
        t('ROL AX,1 (0x8001→0x0003)', [0xB8, 0x01, 0x80, 0xD1, 0xC0, HLT], c => c.reg.ax === 0x0003 && c.reg.getFlag(CF));
        t('ROR AX,1 (0x8001→0xC000)', [0xB8, 0x01, 0x80, 0xD1, 0xC8, HLT], c => c.reg.ax === 0xC000 && c.reg.getFlag(CF));
        t('RCL AL,1 CF=1', [0xF9, 0xB0, 0x00, 0xD0, 0xD0, HLT], c => c.reg.al === 1 && !c.reg.getFlag(CF));
        t('RCR AL,1 CF=1', [0xF9, 0xB0, 0x00, 0xD0, 0xD8, HLT], c => c.reg.al === 0x80 && !c.reg.getFlag(CF));
        t('SHL imm8 (C1)', [0xB8, 0x01, 0x00, 0xC1, 0xE0, 0x08, HLT], c => c.reg.ax === 0x0100);
        t('SHL [BX+01],1', [0xBB, 0x00, 0x01, 0xC6, 0x47, 0x01, 0x42, 0xD0, 0x67, 0x01, HLT], (c, m) => m.read8(0x0101) === 0x84);
    });
    // ================================================================
    // 条件分岐
    // ================================================================
    group('Jcc', t => {
        // 各テスト: 条件成立→BX=0xAA, 不成立→BX=0x00のまま
        const jccTest = (name, setup, jccOp, shouldJump) => {
            // setup → Jcc +04 → MOV BX,0 → HLT → MOV BX,0xAA → HLT
            const code = [...setup, jccOp, 0x04, 0xBB, 0x00, 0x00, HLT, 0xBB, 0xAA, 0x00, HLT];
            return [name, code, c => shouldJump ? c.reg.bx === 0xAA : c.reg.bx === 0];
        };
        // ZF tests
        t(...jccTest('JZ taken', [0xB8, 0x05, 0x00, 0x3D, 0x05, 0x00], 0x74, true));
        t(...jccTest('JZ not taken', [0xB8, 0x05, 0x00, 0x3D, 0x03, 0x00], 0x74, false));
        t(...jccTest('JNZ taken', [0xB8, 0x05, 0x00, 0x3D, 0x03, 0x00], 0x75, true));
        t(...jccTest('JNZ not taken', [0xB8, 0x05, 0x00, 0x3D, 0x05, 0x00], 0x75, false));
        // CF tests
        t(...jccTest('JB/JC taken', [0xB0, 0x01, 0x2C, 0x02], 0x72, true));
        t(...jccTest('JAE/JNC taken', [0xB0, 0x05, 0x2C, 0x02], 0x73, true));
        // SF tests
        t(...jccTest('JS taken', [0xB8, 0x01, 0x00, 0x2D, 0x02, 0x00], 0x78, true));
        t(...jccTest('JNS taken', [0xB8, 0x05, 0x00, 0x2D, 0x02, 0x00], 0x79, true));
        // OF test
        t(...jccTest('JO taken', [0xB8, 0xFF, 0x7F, 0x05, 0x01, 0x00], 0x70, true));
        // JG/JL (signed)
        t(...jccTest('JG taken (5>3)', [0xB8, 0x05, 0x00, 0x3D, 0x03, 0x00], 0x7F, true));
        t(...jccTest('JL taken (1<2 signed)', [0xB8, 0x01, 0x00, 0x3D, 0x02, 0x00], 0x7C, true));
        // JBE/JA (unsigned)
        t(...jccTest('JA taken (5u>3u)', [0xB8, 0x05, 0x00, 0x3D, 0x03, 0x00], 0x77, true));
        t(...jccTest('JBE taken (equal)', [0xB8, 0x05, 0x00, 0x3D, 0x05, 0x00], 0x76, true));
        // 後方ジャンプ (signed offset)
        t('JMP backward', [0xBB, 0x00, 0x00, 0x43, 0x83, 0xFB, 0x03, 0x7C, 0xFA, HLT], c => c.reg.bx === 3);
    });
    // ================================================================
    // LOOP / LOOPE / LOOPNE
    // ================================================================
    group('LOOP', t => {
        t('LOOP 5回', [0xB9, 0x05, 0x00, 0xB8, 0x00, 0x00, 0x40, 0xE2, 0xFD, HLT], c => c.reg.ax === 5 && c.reg.cx === 0);
        t('LOOP 1回', [0xB9, 0x01, 0x00, 0xB8, 0x00, 0x00, 0x40, 0xE2, 0xFD, HLT], c => c.reg.ax === 1 && c.reg.cx === 0);
        t('JCXZ taken', [0xB9, 0x00, 0x00, 0xE3, 0x04, 0xBB, 0x00, 0x00, HLT, 0xBB, 0xAA, 0x00, HLT], c => c.reg.bx === 0xAA);
        t('JCXZ not taken', [0xB9, 0x01, 0x00, 0xE3, 0x04, 0xBB, 0xAA, 0x00, HLT, 0xBB, 0x00, 0x00, HLT], c => c.reg.bx === 0xAA);
    });
    // ================================================================
    // PUSH / POP / PUSHA / POPA
    // ================================================================
    group('Stack', t => {
        t('PUSH/POP AX', [0xB8, 0x34, 0x12, 0x50, 0xB8, 0x00, 0x00, 0x58, HLT], c => c.reg.ax === 0x1234 && c.reg.sp === 0xFFFE);
        t('PUSH/POP multiple', [
            0xB8, 0x11, 0x11, 0xBB, 0x22, 0x22, 0xB9, 0x33, 0x33,
            0x50, 0x53, 0x51, // PUSH AX,BX,CX
            0xB8, 0x00, 0x00, 0xBB, 0x00, 0x00, 0xB9, 0x00, 0x00,
            0x59, 0x5B, 0x58, // POP CX,BX,AX
            HLT
        ], c => c.reg.ax === 0x1111 && c.reg.bx === 0x2222 && c.reg.cx === 0x3333);
        t('PUSH imm16', [0x68, 0xEF, 0xBE, 0x58, HLT], c => c.reg.ax === 0xBEEF);
        t('PUSH imm8 sign-extend', [0x6A, 0xFF, 0x58, HLT], c => c.reg.ax === 0xFFFF);
        t('PUSH/POP seg', [0xB8, 0x00, 0x10, 0x8E, 0xD8, 0x1E, 0xB8, 0x00, 0x00, 0x8E, 0xD8, 0x1F, HLT], c => c.reg.ds === 0x1000);
        t('PUSHF/POPF', [0xF9, 0x9C, 0xF8, 0x9D, HLT], c => c.reg.getFlag(CF));
    });
    // ================================================================
    // CALL / RET
    // ================================================================
    group('CALL/RET', t => {
        t('CALL near/RET', [
            0xE8, 0x02, 0x00, // CALL +2
            HLT, // ← RETで戻る
            0x90,
            0xB8, 0x42, 0x00, // MOV AX, 0x42
            0xC3, // RET
        ], c => c.reg.ax === 0x42);
        t('CALL r16', [
            0xBB, 0x06, 0x00, // MOV BX, 6
            0xFF, 0xD3, // CALL BX
            HLT,
            0xB8, 0x99, 0x00, // MOV AX, 0x99
            0xC3,
        ], c => c.reg.ax === 0x99);
        t('RET imm16 (SP+=n)', [
            0x68, 0xAA, 0xBB, // PUSH 0xBBAA
            0xE8, 0x02, 0x00, // CALL +2
            HLT, 0x90,
            0xC2, 0x02, 0x00, // RET 2 (pop arg)
        ], c => c.reg.sp === 0xFFFE);
    });
    // ================================================================
    // 文字列命令 + REP
    // ================================================================
    group('String ops', t => {
        t('LODSB', [
            0xBE, 0x10, 0x00, // MOV SI, 0x10
            0xC6, 0x06, 0x10, 0x00, 0x42, // MOV BYTE [0x10], 0x42
            0xAC, // LODSB
            HLT
        ], c => c.reg.al === 0x42 && c.reg.si === 0x11);
        t('STOSB', [
            0xBF, 0x00, 0x02, // MOV DI, 0x200
            0xB0, 0xAA, // MOV AL, 0xAA
            0xAA, // STOSB
            HLT
        ], (c, m) => m.read8(0x200) === 0xAA && c.reg.di === 0x201);
        t('REP STOSB', [
            0xBF, 0x00, 0x02, // MOV DI, 0x200
            0xB9, 0x04, 0x00, // MOV CX, 4
            0xB0, 0xFF, // MOV AL, 0xFF
            0xF3, 0xAA, // REP STOSB
            HLT
        ], (c, m) => m.read8(0x200) === 0xFF && m.read8(0x203) === 0xFF && c.reg.cx === 0 && c.reg.di === 0x204);
        t('REP MOVSB', [
            0xBE, 0x00, 0x01, // MOV SI, 0x100
            0xBF, 0x00, 0x02, // MOV DI, 0x200
            0xB9, 0x03, 0x00, // MOV CX, 3
            0xC6, 0x06, 0x00, 0x01, 0x41,
            0xC6, 0x06, 0x01, 0x01, 0x42,
            0xC6, 0x06, 0x02, 0x01, 0x43,
            0xF3, 0xA4, // REP MOVSB
            HLT
        ], (c, m) => m.read8(0x200) === 0x41 && m.read8(0x201) === 0x42 && m.read8(0x202) === 0x43);
        t('LODSB+DF=1 (backward)', [
            0xFD, // STD
            0xBE, 0x12, 0x00, // MOV SI, 0x12
            0xC6, 0x06, 0x12, 0x00, 0x99,
            0xAC, // LODSB
            HLT
        ], c => c.reg.al === 0x99 && c.reg.si === 0x11);
    });
    // ================================================================
    // LEA / XCHG / CBW / CWD
    // ================================================================
    group('LEA/XCHG/CBW/CWD', t => {
        t('LEA BX,[SI+10h]', [0xBE, 0x00, 0x01, 0x8D, 0x5C, 0x10, HLT], c => c.reg.bx === 0x0110);
        t('XCHG AX,BX', [0xB8, 0x11, 0x11, 0xBB, 0x22, 0x22, 0x93, HLT], c => c.reg.ax === 0x2222 && c.reg.bx === 0x1111);
        t('XCHG r8,r8', [0xB0, 0xAA, 0xB3, 0xBB, 0x86, 0xC3, HLT], c => c.reg.al === 0xBB && c.reg.bl === 0xAA);
        t('CBW positive', [0xB0, 0x42, 0x98, HLT], c => c.reg.ax === 0x0042);
        t('CBW negative', [0xB0, 0x80, 0x98, HLT], c => c.reg.ax === 0xFF80);
        t('CWD positive', [0xB8, 0x00, 0x10, 0x99, HLT], c => c.reg.dx === 0);
        t('CWD negative', [0xB8, 0x00, 0x80, 0x99, HLT], c => c.reg.dx === 0xFFFF);
    });
    // ================================================================
    // INT / IRET (ハンドラ) — カスタムテスト
    // ================================================================
    // INTテストをカスタムで追加
    {
        const tests = [];
        // INT 10h output test
        {
            const m = new Memory();
            const c = new CPU8086(m);
            let output = '';
            c.registerInterrupt(0x10, () => { if (c.reg.ah === 0x0E)
                output += String.fromCharCode(c.reg.al); });
            c.registerInterrupt(0x21, () => { if (c.reg.ah === 0x4C)
                c.halted = true; });
            m.load(0x100, [
                0xBE, 0x10, 0x01,
                0xAC, 0xA8, 0xFF, 0x74, 0x06, 0xB4, 0x0E, 0xCD, 0x10, 0xEB, 0xF5,
                0xB8, 0x00, 0x4C, 0xCD, 0x21,
            ]);
            m.load(0x110, [0x48, 0x69, 0x00]); // "Hi\0"
            c.reg.cs = 0;
            c.reg.ip = 0x100;
            c.reg.ds = 0;
            c.reg.ss = 0;
            c.reg.sp = 0xFFFE;
            c.run(100000);
            const ok = output === 'Hi';
            tests.push({ name: 'INT 10h Hello', pass: ok });
            if (ok)
                totalPass++;
            else
                totalFail++;
        }
        // INT 21h/09 string output
        {
            const m = new Memory();
            const c = new CPU8086(m);
            let output = '';
            c.registerInterrupt(0x21, () => {
                if (c.reg.ah === 0x09) {
                    let a = c.reg.segmented(c.reg.ds, c.reg.dx);
                    let ch, lim = 0;
                    while ((ch = m.read8(a++)) !== 0x24 && lim++ < 100)
                        output += String.fromCharCode(ch);
                }
                if (c.reg.ah === 0x4C)
                    c.halted = true;
            });
            m.load(0x100, [
                0xBA, 0x0C, 0x01, // MOV DX, 0x10C
                0xB4, 0x09, // MOV AH, 09
                0xCD, 0x21, // INT 21h
                0xB8, 0x00, 0x4C, // MOV AX, 4C00h
                0xCD, 0x21,
            ]);
            m.load(0x10C, [0x4F, 0x4B, 0x24]); // "OK$"
            c.reg.cs = 0;
            c.reg.ip = 0x100;
            c.reg.ds = 0;
            c.reg.ss = 0;
            c.reg.sp = 0xFFFE;
            c.run(100000);
            const ok = output === 'OK';
            tests.push({ name: 'INT 21h/09 print$', pass: ok });
            if (ok)
                totalPass++;
            else
                totalFail++;
        }
        let p = 0, f = 0;
        tests.forEach(t => { if (t.pass)
            p++;
        else
            f++; });
        groups.push({ group: 'INT', tests, passCount: p, failCount: f });
    }
    // ================================================================
    // フラグ操作
    // ================================================================
    group('Flags', t => {
        t('STC', [0xF9, HLT], c => c.reg.getFlag(CF));
        t('CLC', [0xF9, 0xF8, HLT], c => !c.reg.getFlag(CF));
        t('CMC', [0xF9, 0xF5, HLT], c => !c.reg.getFlag(CF));
        t('CMC×2', [0xF5, 0xF5, HLT], c => !c.reg.getFlag(CF));
        t('STD', [0xFD, HLT], c => c.reg.getFlag(DF));
        t('CLD', [0xFD, 0xFC, HLT], c => !c.reg.getFlag(DF));
        t('STI', [0xFB, HLT], c => c.reg.getFlag(FLAGS.IF));
        t('CLI', [0xFB, 0xFA, HLT], c => !c.reg.getFlag(FLAGS.IF));
        t('LAHF/SAHF', [0xF9, 0x9F, 0xF8, 0xB4, 0xD5, 0x9E, HLT], c => c.reg.getFlag(CF)); // SAHF restores CF from AH
    });
    // ================================================================
    // NOP / HLT / XLAT
    // ================================================================
    group('Misc', t => {
        t('NOP (IP advances)', [0x90, 0x90, 0x90, 0xB8, 0x42, 0x00, HLT], c => c.reg.ax === 0x42);
        t('XLAT', [
            0xBB, 0x00, 0x01, // MOV BX, 0x100
            0xB0, 0x03, // MOV AL, 3
            0xC6, 0x06, 0x03, 0x01, 0x42, // MOV BYTE [0x103], 0x42
            0xD7, // XLAT
            HLT
        ], c => c.reg.al === 0x42);
        t('AAM', [0xB0, 0x37, 0xD4, 0x0A, HLT], c => c.reg.ah === 5 && c.reg.al === 5); // 55/10=5 rem 5
        t('AAD', [0xB4, 0x05, 0xB0, 0x03, 0xD5, 0x0A, HLT], c => c.reg.al === 53 && c.reg.ah === 0); // 5*10+3
        t('DAA', [0xB0, 0x99, 0x04, 0x01, 0x27, HLT], c => c.reg.al === 0x00 && c.reg.getFlag(CF)); // 99+01=100 BCD
    });
    // ================================================================
    // ENTER / LEAVE
    // ================================================================
    group('ENTER/LEAVE', t => {
        t('ENTER 4,0 / LEAVE', [
            0xC8, 0x04, 0x00, 0x00, // ENTER 4, 0
            0xC9, // LEAVE
            HLT
        ], c => c.reg.sp === 0xFFFE && c.reg.bp === 0);
    });
    // ================================================================
    // 0F プレフィックス命令
    // ================================================================
    group('0F prefix', t => {
        t('MOVZX r16,r/m8 (0F B6)', [0xB3, 0x80, 0x0F, 0xB6, 0xC3, HLT], c => c.reg.ax === 0x0080);
        t('MOVSX r16,r/m8 (0F BE)', [0xB3, 0x80, 0x0F, 0xBE, 0xC3, HLT], c => c.reg.ax === 0xFF80);
        t('BSF (0F BC)', [0xBB, 0x08, 0x00, 0x0F, 0xBC, 0xC3, HLT], c => c.reg.ax === 3);
        t('BSR (0F BD)', [0xBB, 0x08, 0x00, 0x0F, 0xBD, 0xC3, HLT], c => c.reg.ax === 3);
    });
    // ================================================================
    // read-modify-write EAテスト
    // ================================================================
    group('EA cache', t => {
        t('ADD BYTE [BX+02],05', [0xBB, 0x00, 0x01, 0xC6, 0x47, 0x02, 0x0A, 0x80, 0x47, 0x02, 0x05, HLT], (c, m) => m.read8(0x0102) === 0x0F);
        t('ADD WORD [BX+02],1000h', [0xBB, 0x00, 0x01, 0xC7, 0x47, 0x02, 0x34, 0x02, 0x81, 0x47, 0x02, 0x00, 0x10, HLT], (c, m) => m.read16(0x0102) === 0x1234);
        t('OR [BX+02],AL', [0xBB, 0x00, 0x01, 0xB0, 0xF0, 0xC6, 0x47, 0x02, 0x0A, 0x08, 0x47, 0x02, HLT], (c, m) => m.read8(0x0102) === 0xFA);
        t('NEG BYTE [BX+01]', [0xBB, 0x00, 0x01, 0xC6, 0x47, 0x01, 0x05, 0xF6, 0x5F, 0x01, HLT], (c, m) => m.read8(0x0101) === 0xFB);
        t('NOT WORD [BX+02]', [0xBB, 0x00, 0x01, 0xC7, 0x47, 0x02, 0x00, 0xFF, 0xF7, 0x57, 0x02, HLT], (c, m) => m.read16(0x0102) === 0x00FF);
        t('SHL WORD [BX+02],CL', [0xBB, 0x00, 0x01, 0xB1, 0x04, 0xC7, 0x47, 0x02, 0x01, 0x00, 0xD3, 0x67, 0x02, HLT], (c, m) => m.read16(0x0102) === 0x0010);
    });
    group('自作プログラム実行テスト', t => {
        // 文字出力の過程をレジスタで確認するテスト
        // ※画面に「PASS!」と出るかは目視、テストとしては「終了まで到達したか」を確認
        t('Run PASS! Code', [
            0xB4, 0x0E, // MOV AH, 0x0E
            0xB0, 0x50, 0xCD, 0x10, // 'P'
            0xB0, 0x41, 0xCD, 0x10, // 'A'
            0xB0, 0x53, 0xCD, 0x10, // 'S'
            0xB0, 0x53, 0xCD, 0x10, // 'S'
            0xB0, 0x21, 0xCD, 0x10, // '!'
            0xB4, 0x4C, 0xCD, 0x21 // INT 21h (AH=4Ch)
        ], (c) => {
            // 最後に実行された文字が '!' (0x21) かつ AH=4Ch で終了しているか
            return c.reg.al === 0x21 && c.reg.ah === 0x4C;
        });
        // ループ計算のテスト（これは引数2つの型に合致し、ロジックも正確です）
        // 計算結果(15)を出すテスト
        t('Calc 1+2+3+4+5', [
            0xB8, 0x00, 0x00, // MOV AX, 0
            0xB9, 0x05, 0x00, // MOV CX, 5
            // <loop_start>
            0x01, 0xC8, // ADD AX, CX
            0x49, // DEC CX
            0x75, 0xFB, // JNZ <loop_start>
            0xB4, 0x4C, 0xCD, 0x21 // AHを4Ch(76)に書き換えて終了
        ], (c) => {
            // AX全体(c.reg.ax)は 0x4C0F になっているので、
            // 下位8bitの AL だけをチェックして 15 (0Fh) か確認する
            return c.reg.al === 15;
        });
    });
    return { groups, totalPass, totalFail };
}