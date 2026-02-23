'use strict';
// ============================================================
// FAT12 仮想ディスク — セクタ単位 localStorage
// ============================================================
class FAT12Disk {
  constructor() {
    this.SECTOR_SIZE        = 512;
    this.TOTAL_SECTORS      = 2880;
    this.SECTORS_PER_FAT   = 9;
    this.NUM_FATS           = 2;
    this.ROOT_ENTRY_COUNT   = 224;
    this.SECTORS_PER_CLUSTER= 1;
    this.RESERVED_SECTORS   = 1;
    this.FAT1_START  = 1;
    this.FAT2_START  = 1 + this.SECTORS_PER_FAT;
    this.ROOT_START  = 1 + this.SECTORS_PER_FAT * 2;
    this.ROOT_SECTORS= Math.ceil(this.ROOT_ENTRY_COUNT * 32 / this.SECTOR_SIZE);
    this.DATA_START  = this.ROOT_START + this.ROOT_SECTORS;
    this._cache = {};
    this._dirty = new Set();
  }
  _sec(n) {
    if (!this._cache[n]) {
      const b64 = localStorage.getItem(`msdos_s${n}`);
      if (b64) {
        const bin = atob(b64);
        const arr = new Uint8Array(512);
        for (let i=0;i<512;i++) arr[i]=bin.charCodeAt(i);
        this._cache[n]=arr;
      } else {
        this._cache[n]=new Uint8Array(512);
      }
    }
    return this._cache[n];
  }
  r8(s,o)     { return this._sec(s)[o]; }
  w8(s,o,v)   { this._sec(s)[o]=v&0xFF; this._dirty.add(s); }
  r16(s,o)    { return this.r8(s,o)|(this.r8(s,o+1)<<8); }
  w16(s,o,v)  { this.w8(s,o,v&0xFF); this.w8(s,o+1,(v>>8)&0xFF); }
  r32(s,o)    { return (this.r16(s,o)|(this.r16(s,o+2)<<16))>>>0; }
  w32(s,o,v)  { this.w16(s,o,v&0xFFFF); this.w16(s,o+2,(v>>>16)&0xFFFF); }
  flush() {
    for (const n of this._dirty) {
      const sec=this._sec(n);
      let bin='';
      for (let i=0;i<512;i++) bin+=String.fromCharCode(sec[i]);
      localStorage.setItem(`msdos_s${n}`,btoa(bin));
    }
    this._dirty.clear();
  }
  wipeStorage() {
    for (let n=0;n<this.TOTAL_SECTORS;n++) localStorage.removeItem(`msdos_s${n}`);
    this._cache={};
    this._dirty.clear();
  }
  isFormatted() { return this.r8(0,0)===0xEB; }
  format() {
    this.wipeStorage();
    const b=this._sec(0);
    b[0]=0xEB;b[1]=0x3C;b[2]=0x90;
    const oem='MYDOS1.0';for(let i=0;i<8;i++) b[3+i]=oem.charCodeAt(i);
    this.w16(0,11,512);b[13]=1;this.w16(0,14,1);b[16]=2;this.w16(0,17,224);
    this.w16(0,19,2880);b[21]=0xF0;this.w16(0,22,9);this.w16(0,24,18);this.w16(0,26,2);
    this.w8(this.FAT1_START,0,0xF0);this.w8(this.FAT1_START,1,0xFF);this.w8(this.FAT1_START,2,0xFF);
    this.w8(this.FAT2_START,0,0xF0);this.w8(this.FAT2_START,1,0xFF);this.w8(this.FAT2_START,2,0xFF);
    this.flush();
  }
  getFAT(c) {
    const off=c+(c>>1);const sec=this.FAT1_START+Math.floor(off/512);const o=off%512;
    let v=this.r8(sec,o)|((o+1<512?this.r8(sec,o+1):this.r8(sec+1,0))<<8);
    return(c&1)?v>>4:v&0xFFF;
  }
  setFAT(c,val) {
    const off=c+(c>>1);const sec=this.FAT1_START+Math.floor(off/512);const o=off%512;
    let cur=this.r8(sec,o)|((o+1<512?this.r8(sec,o+1):this.r8(sec+1,0))<<8);
    if(c&1){cur=(cur&0x000F)|(val<<4);}else{cur=(cur&0xF000)|(val&0xFFF);}
    this.w8(sec,o,cur&0xFF);
    if(o+1<512)this.w8(sec,o+1,(cur>>8)&0xFF);else this.w8(sec+1,0,(cur>>8)&0xFF);
    const s2=this.FAT2_START+Math.floor(off/512);const o2=off%512;
    this.w8(s2,o2,cur&0xFF);
    if(o2+1<512)this.w8(s2,o2+1,(cur>>8)&0xFF);else this.w8(s2+1,0,(cur>>8)&0xFF);
  }
  allocCluster() {
    const max=Math.floor(this.SECTORS_PER_FAT*512*2/3);
    for(let c=2;c<max;c++){if(this.getFAT(c)===0)return c;}
    return -1;
  }
  freeClusters() {
    const max=Math.floor(this.SECTORS_PER_FAT*512*2/3);
    let f=0;for(let c=2;c<max;c++){if(this.getFAT(c)===0)f++;}return f;
  }
  c2s(c){return this.DATA_START+c-2;}
  _resolveDirSectors(parts) {
    if(!parts.length) {
      const a=[];for(let i=0;i<this.ROOT_SECTORS;i++) a.push(this.ROOT_START+i);return a;
    }
    let secs=[];for(let i=0;i<this.ROOT_SECTORS;i++) secs.push(this.ROOT_START+i);
    for(const name of parts) {
      const entries=this._enumEntries(secs);
      const d=entries.find(e=>(e.attr&0x10)&&e.name.toUpperCase()===name.toUpperCase());
      if(!d) return null;
      secs=[];let c=d.cluster;
      while(c>=2&&c<0xFF8){secs.push(this.c2s(c));c=this.getFAT(c);}
      if(!secs.length) return null;
    }
    return secs;
  }
  _enumEntries(secs) {
    const res=[];
    for(const sec of secs){
      for(let slot=0;slot<16;slot++){
        const f=this.r8(sec,slot*32);
        if(f===0x00)return res;if(f===0xE5)continue;
        const attr=this.r8(sec,slot*32+11);
        if(attr===0x0F)continue;
        res.push(this._readEntry(sec,slot));
      }
    }
    return res;
  }
  _readEntry(sec,slot) {
    const off=slot*32;
    let n='';
    for(let i=0;i<8;i++){const c=this.r8(sec,off+i);if(c===0x20)break;n+=String.fromCharCode(c);}
    let e='';
    for(let i=8;i<11;i++){const c=this.r8(sec,off+i);if(c===0x20)break;e+=String.fromCharCode(c);}
    return {
      first:this.r8(sec,off),
      name:e?n+'.'+e:n,
      attr:this.r8(sec,off+11),
      cluster:this.r16(sec,off+26),
      size:this.r32(sec,off+28),
      sec,slot
    };
  }
  _writeName83(sec,off,name) {
    const dot=name.lastIndexOf('.');
    let n=(dot>=0?name.slice(0,dot):name).toUpperCase().slice(0,8);
    let e=(dot>=0?name.slice(dot+1):'').toUpperCase().slice(0,3);
    for(let i=0;i<8;i++) this.w8(sec,off+i,i<n.length?n.charCodeAt(i):0x20);
    for(let i=0;i<3;i++) this.w8(sec,off+8+i,i<e.length?e.charCodeAt(i):0x20);
  }
  _allocEntry(sectors) {
    for(const sec of sectors) {
      for(let slot=0;slot<16;slot++) {
        const f=this.r8(sec,slot*32);
        if(f===0x00||f===0xE5) return {sec,slot};
      }
    }
    return {sec:-1,slot:0};
  }
  listDir(parts=[]) {
    const secs=this._resolveDirSectors(parts);
    if(!secs) return null;
    return this._enumEntries(secs).filter(e=>!(e.attr&0x08));
  }
  readFile(parts,name) {
    const secs=this._resolveDirSectors(parts);
    if(!secs) return null;
    const f=this._enumEntries(secs).find(e=>!(e.attr&0x10)&&e.name.toUpperCase()===name.toUpperCase());
    if(!f) return null;
    const buf=[];let c=f.cluster,rem=f.size;
    while(c>=2&&c<0xFF8){
      const sec=this.c2s(c);const take=Math.min(512,rem);
      for(let i=0;i<take;i++) buf.push(this.r8(sec,i));
      rem-=take;c=this.getFAT(c);
    }
    return new Uint8Array(buf);
  }
  writeFile(parts,name,data) {
    this.deleteEntry(parts,name);
    const secs=this._resolveDirSectors(parts);
    if(!secs) throw new Error('Directory not found');
    let first=-1,prev=-1,off=0;
    if(data.length>0) {
      while(off<data.length) {
        const c=this.allocCluster();
        if(c<0) throw new Error('Disk full');
        if(first<0) first=c;
        if(prev>=0) this.setFAT(prev,c);
        const sec=this.c2s(c);
        for(let i=0;i<512;i++) this.w8(sec,i,0);
        const take=Math.min(512,data.length-off);
        for(let i=0;i<take;i++) this.w8(sec,i,data[off+i]);
        off+=take;prev=c;
      }
      this.setFAT(prev,0xFFF);
    }
    const {sec,slot}=this._allocEntry(secs);
    if(sec<0) throw new Error('Directory full');
    const eoff=slot*32;
    for(let i=0;i<32;i++) this.w8(sec,eoff+i,0);
    this._writeName83(sec,eoff,name);
    this.w8(sec,eoff+11,0x20);
    const now=new Date();
    const time=((now.getHours()&31)<<11)|((now.getMinutes()&63)<<5)|((now.getSeconds()>>1)&31);
    const date=(((now.getFullYear()-1980)&127)<<9)|((now.getMonth()+1)<<5)|(now.getDate()&31);
    this.w16(sec,eoff+22,time);this.w16(sec,eoff+24,date);
    this.w16(sec,eoff+26,first<0?0:first);
    this.w32(sec,eoff+28,data.length);
    this.flush();
  }
  deleteEntry(parts,name) {
    const secs=this._resolveDirSectors(parts);
    if(!secs) return false;
    const entries=this._enumEntries(secs);
    const f=entries.find(e=>e.name.toUpperCase()===name.toUpperCase());
    if(!f) return false;
    this.w8(f.sec,f.slot*32,0xE5);
    let c=f.cluster;
    while(c>=2&&c<0xFF8){const n=this.getFAT(c);this.setFAT(c,0);c=n;}
    this.flush();
    return true;
  }
  renameEntry(parts,oldName,newName) {
    const secs=this._resolveDirSectors(parts);
    if(!secs)return false;
    const f=this._enumEntries(secs).find(e=>e.name.toUpperCase()===oldName.toUpperCase());
    if(!f)return false;
    this._writeName83(f.sec,f.slot*32,newName);
    this.flush();return true;
  }
  mkdir(parts,name) {
    const secs=this._resolveDirSectors(parts);
    if(!secs) throw new Error('Path not found');
    const existing=this._enumEntries(secs).find(e=>e.name.toUpperCase()===name.toUpperCase());
    if(existing) throw new Error('Already exists');
    const c=this.allocCluster();
    if(c<0) throw new Error('Disk full');
    this.setFAT(c,0xFFF);
    const dsec=this.c2s(c);
    for(let i=0;i<512;i++) this.w8(dsec,i,0);
    const {sec,slot}=this._allocEntry(secs);
    if(sec<0) throw new Error('Directory full');
    const eoff=slot*32;
    for(let i=0;i<32;i++) this.w8(sec,eoff+i,0);
    this._writeName83(sec,eoff,name);
    this.w8(sec,eoff+11,0x10);
    const now=new Date();
    const time=((now.getHours()&31)<<11)|((now.getMinutes()&63)<<5)|((now.getSeconds()>>1)&31);
    const date=(((now.getFullYear()-1980)&127)<<9)|((now.getMonth()+1)<<5)|(now.getDate()&31);
    this.w16(sec,eoff+22,time);this.w16(sec,eoff+24,date);
    this.w16(sec,eoff+26,c);
    this.w32(sec,eoff+28,0);
    this.flush();
  }
  download(fn) {
    const all=[];
    for(let s=0;s<this.TOTAL_SECTORS;s++){const sec=this._sec(s);for(let i=0;i<512;i++)all.push(sec[i]);}
    const blob=new Blob([new Uint8Array(all)],{type:'application/octet-stream'});
    const a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=fn;a.click();
  }
}

// ============================================================
// EDIT — フルスクリーンテキストエディタ
// ============================================================
class DosEdit {
  constructor(disk, cwdParts, term) {
    this.disk = disk;
    this.cwdParts = cwdParts;
    this.term = term;
    this.lines = [''];
    this.cx = 0;        // カーソル列
    this.cy = 0;        // カーソル行
    this.scrollY = 0;   // スクロールオフセット
    this.ROWS = 23;     // エディタ表示行数（上1行メニュー、下1行ステータス）
    this.COLS = 80;
    this.filename = '';
    this.modified = false;
    this.active = false;
    this.onExit = null;   // 終了コールバック
    this.message = '';
    this.inputMode = null;  // null | 'save_as' | 'confirm_quit' | 'confirm_new'
    this.inputBuf = '';
  }

  open(filename) {
    this.filename = (filename || '').toUpperCase();
    if (this.filename) {
      const parts = this.filename.replace(/^A:\\/i, '').split('\\').filter(Boolean);
      const fn = parts.pop();
      const dp = parts.map(s => s.toUpperCase());
      const data = this.disk.readFile([...this.cwdParts, ...dp], fn);
      if (data) {
        const text = new TextDecoder().decode(data).replace(/\r\n/g, '\n').replace(/\r/g, '\n');
        this.lines = text.split('\n');
        if (this.lines.length === 0) this.lines = [''];
        this.message = `${fn} (${data.length} bytes) を読み込みました`;
      } else {
        this.lines = [''];
        this.message = '新規ファイル';
      }
    } else {
      this.lines = [''];
      this.message = '新規ファイル - 名前未設定';
    }
    this.cx = 0; this.cy = 0; this.scrollY = 0;
    this.modified = false;
    this.active = true;
    this.inputMode = null;
    this.render();
  }

  render() {
    // 80x25 テキスト画面を生成
    const buf = [];
    // === Menu bar (row 0) ===
    const menu = ' File  Edit                                          MYDOS EDIT';
    buf.push(this._invLine(menu));
    // === Editor area (rows 1-23) ===
    for (let i = 0; i < this.ROWS; i++) {
      const lineIdx = this.scrollY + i;
      if (lineIdx < this.lines.length) {
        let ln = this.lines[lineIdx];
        if (ln.length > this.COLS) ln = ln.slice(0, this.COLS);
        buf.push(ln + ' '.repeat(Math.max(0, this.COLS - ln.length)));
      } else {
        buf.push('~' + ' '.repeat(this.COLS - 1));
      }
    }
    // === Status bar (row 24) ===
    let status;
    if (this.inputMode === 'save_as') {
      status = ` Save as: ${this.inputBuf}_`;
    } else if (this.inputMode === 'confirm_quit') {
      status = ` ファイルが変更されています。保存しますか? (Y/N/Esc)`;
    } else if (this.inputMode === 'confirm_new') {
      status = ` 変更を破棄して新規作成しますか? (Y/N)`;
    } else {
      const fn = this.filename || '(無題)';
      const mod = this.modified ? ' [変更あり]' : '';
      const pos = `行:${this.cy + 1} 列:${this.cx + 1}`;
      const msg = this.message ? `  ${this.message}` : '';
      status = ` ${fn}${mod}  ${pos}${msg}`;
    }
    buf.push(this._invLine(status));

    // 出力
    if (window._editRender) {
      window._editRender(buf.join('\n'), this.cy - this.scrollY + 1, this.cx);
    }
  }

  _invLine(s) {
    return (s + ' '.repeat(Math.max(0, this.COLS - s.length))).slice(0, this.COLS);
  }

  onKey(key, ctrl, shift) {
    this.message = '';
    // Input mode handlers
    if (this.inputMode === 'save_as') {
      if (key === 'Escape') { this.inputMode = null; this.render(); return; }
      if (key === 'Enter') { this._doSave(this.inputBuf); this.inputMode = null; this.render(); return; }
      if (key === 'Backspace') { this.inputBuf = this.inputBuf.slice(0, -1); this.render(); return; }
      if (key.length === 1) { this.inputBuf += key; this.render(); return; }
      return;
    }
    if (this.inputMode === 'confirm_quit') {
      if (key === 'y' || key === 'Y') { this._doSave(this.filename); this._exit(); return; }
      if (key === 'n' || key === 'N') { this._exit(); return; }
      if (key === 'Escape') { this.inputMode = null; this.render(); return; }
      return;
    }
    if (this.inputMode === 'confirm_new') {
      if (key === 'y' || key === 'Y') { this.lines = ['']; this.cx = 0; this.cy = 0; this.scrollY = 0; this.filename = ''; this.modified = false; this.inputMode = null; this.message = '新規ファイル'; this.render(); return; }
      if (key === 'n' || key === 'N' || key === 'Escape') { this.inputMode = null; this.render(); return; }
      return;
    }

    // Ctrl shortcuts
    if (ctrl) {
      switch (key) {
        case 's': case 'S': // Save
          if (!this.filename) { this.inputMode = 'save_as'; this.inputBuf = ''; }
          else this._doSave(this.filename);
          this.render(); return;
        case 'o': case 'O': // Open (save as)
          this.inputMode = 'save_as'; this.inputBuf = this.filename || '';
          this.render(); return;
        case 'n': case 'N': // New
          if (this.modified) { this.inputMode = 'confirm_new'; }
          else { this.lines = ['']; this.cx = 0; this.cy = 0; this.scrollY = 0; this.filename = ''; this.modified = false; this.message = '新規ファイル'; }
          this.render(); return;
        case 'q': case 'Q': case 'w': case 'W': // Quit
          if (this.modified) { this.inputMode = 'confirm_quit'; this.render(); return; }
          this._exit(); return;
        case 'g': case 'G': // Go to line (simple)
          return;
      }
      return;
    }

    // Normal keys
    switch (key) {
      case 'Escape':
        if (this.modified) { this.inputMode = 'confirm_quit'; this.render(); return; }
        this._exit(); return;

      case 'ArrowUp':
        if (this.cy > 0) this.cy--;
        this._fixCx(); this._scroll(); this.render(); return;
      case 'ArrowDown':
        if (this.cy < this.lines.length - 1) this.cy++;
        this._fixCx(); this._scroll(); this.render(); return;
      case 'ArrowLeft':
        if (this.cx > 0) this.cx--;
        else if (this.cy > 0) { this.cy--; this.cx = this.lines[this.cy].length; }
        this._scroll(); this.render(); return;
      case 'ArrowRight':
        if (this.cx < this.lines[this.cy].length) this.cx++;
        else if (this.cy < this.lines.length - 1) { this.cy++; this.cx = 0; }
        this._scroll(); this.render(); return;
      case 'Home':
        this.cx = 0; this.render(); return;
      case 'End':
        this.cx = this.lines[this.cy].length; this.render(); return;
      case 'PageUp':
        this.cy = Math.max(0, this.cy - this.ROWS);
        this._fixCx(); this._scroll(); this.render(); return;
      case 'PageDown':
        this.cy = Math.min(this.lines.length - 1, this.cy + this.ROWS);
        this._fixCx(); this._scroll(); this.render(); return;

      case 'Enter':
        this._insertNewline(); this.render(); return;
      case 'Backspace':
        this._backspace(); this.render(); return;
      case 'Delete':
        this._delete(); this.render(); return;
      case 'Tab':
        this._insertText('    '); this.render(); return;

      case 'F1': // Help
        this.message = 'Ctrl+S:保存 Ctrl+Q:終了 Ctrl+N:新規 Esc:終了';
        this.render(); return;

      default:
        if (key.length === 1) { this._insertText(key); this.render(); }
    }
  }

  _insertText(s) {
    const line = this.lines[this.cy];
    this.lines[this.cy] = line.slice(0, this.cx) + s + line.slice(this.cx);
    this.cx += s.length;
    this.modified = true;
  }

  _insertNewline() {
    const line = this.lines[this.cy];
    const before = line.slice(0, this.cx);
    const after = line.slice(this.cx);
    this.lines[this.cy] = before;
    this.lines.splice(this.cy + 1, 0, after);
    this.cy++;
    this.cx = 0;
    this.modified = true;
    this._scroll();
  }

  _backspace() {
    if (this.cx > 0) {
      const line = this.lines[this.cy];
      this.lines[this.cy] = line.slice(0, this.cx - 1) + line.slice(this.cx);
      this.cx--;
      this.modified = true;
    } else if (this.cy > 0) {
      this.cx = this.lines[this.cy - 1].length;
      this.lines[this.cy - 1] += this.lines[this.cy];
      this.lines.splice(this.cy, 1);
      this.cy--;
      this.modified = true;
      this._scroll();
    }
  }

  _delete() {
    const line = this.lines[this.cy];
    if (this.cx < line.length) {
      this.lines[this.cy] = line.slice(0, this.cx) + line.slice(this.cx + 1);
      this.modified = true;
    } else if (this.cy < this.lines.length - 1) {
      this.lines[this.cy] += this.lines[this.cy + 1];
      this.lines.splice(this.cy + 1, 1);
      this.modified = true;
    }
  }

  _fixCx() {
    if (this.cx > this.lines[this.cy].length) this.cx = this.lines[this.cy].length;
  }

  _scroll() {
    if (this.cy < this.scrollY) this.scrollY = this.cy;
    if (this.cy >= this.scrollY + this.ROWS) this.scrollY = this.cy - this.ROWS + 1;
  }

  _doSave(filename) {
    if (!filename) { this.inputMode = 'save_as'; this.inputBuf = ''; return; }
    filename = filename.toUpperCase();
    if (!filename.includes('.')) filename += '.TXT';
    const text = this.lines.join('\r\n');
    const enc = new TextEncoder().encode(text);
    try {
      this.disk.writeFile(this.cwdParts, filename, enc);
      this.disk.flush();
      this.filename = filename;
      this.modified = false;
      this.message = `${filename} を保存しました (${enc.length} bytes)`;
      if (window.onDiskChange) window.onDiskChange();
    } catch (e) {
      this.message = '保存エラー: ' + e.message;
    }
  }

  _exit() {
    this.active = false;
    if (this.onExit) this.onExit();
  }
}

// ============================================================
// COPY CON — コンソール入力モード
// ============================================================
class CopyCon {
  constructor(disk, cwdParts, term, filename) {
    this.disk = disk;
    this.cwdParts = cwdParts;
    this.term = term;
    this.filename = filename.toUpperCase();
    this.linesBuf = [];
    this.active = true;
    this.onExit = null;
  }

  start() {
    this.term.println(`CON → ${this.filename}`);
    this.term.println('(入力してください。Ctrl+Z で保存、Ctrl+C で中止)');
  }

  onLine(line) {
    this.linesBuf.push(line);
  }

  onCtrlZ() {
    const text = this.linesBuf.join('\r\n') + '\r\n';
    const enc = new TextEncoder().encode(text);
    try {
      if (!this.filename.includes('.')) this.filename += '.TXT';
      this.disk.writeFile(this.cwdParts, this.filename, enc);
      this.disk.flush();
      this.term.println('^Z');
      this.term.println(`        1 個のファイルをコピーしました`);
      if (window.onDiskChange) window.onDiskChange();
    } catch (e) {
      this.term.println('書き込みエラー: ' + e.message);
    }
    this.active = false;
    if (this.onExit) this.onExit();
  }

  onCtrlC() {
    this.term.println('^C');
    this.active = false;
    if (this.onExit) this.onExit();
  }
}

// ============================================================
// DOSShell
// ============================================================
class DOSShell {
  constructor(disk, term) {
    this.disk = disk; this.term = term;
    this.cwdParts = [];
    this.env = { PATH: 'A:\\', COMSPEC: 'A:\\COMMAND.COM', PROMPT: '$P$G', TEMP: 'A:\\TEMP' };
    this.history = []; this.histIdx = -1;
    this.echoOn = true;
  }

  cwdStr() { return 'A:\\' + this.cwdParts.join('\\') + (this.cwdParts.length ? '\\' : ''); }

  prompt() {
    let p = this.env.PROMPT || '$P$G';
    const now = new Date();
    p = p.replace(/\$P/gi, this.cwdStr()).replace(/\$G/gi, '>').replace(/\$N/gi, 'A')
       .replace(/\$D/gi, now.toLocaleDateString()).replace(/\$T/gi, now.toLocaleTimeString())
       .replace(/\$V/gi, 'MYDOS 1.0').replace(/\$\$/gi, '$').replace(/\$_/gi, '\n');
    this.term.print(p);
  }

  start() {
    this.term.println('MYDOS Version 1.0');
    this.term.println('Copyright (C) 2025 MyDOS Systems');
    this.term.println('');
    this.prompt();
  }

  execute(line) {
    line = line.trim();
    if (!line) { this.term.println(''); this.prompt(); return; }
    if (line.startsWith('@')) { line = line.slice(1).trim(); }
    this.history.unshift(line); this.histIdx = -1;
    this.term.println('');

    // リダイレクト / パイプ
    let pipeMore = false, redirOut = null, redirAppend = false, cmd = line;
    const pm = line.match(/^(.*?)\s*\|\s*MORE\s*$/i);
    if (pm) { pipeMore = true; cmd = pm[1].trim(); }
    const ra = cmd.match(/^(.*?)\s*>>\s*(\S+)\s*$/);
    if (ra) { redirOut = ra[2]; redirAppend = true; cmd = ra[1].trim(); }
    else {
      const rm = cmd.match(/^(.*?)\s*>\s*(\S+)\s*$/);
      if (rm) { redirOut = rm[2]; cmd = rm[1].trim(); }
    }

    const parts = this._splitArgs(cmd);
    const name = (parts[0] || '').toUpperCase();
    const args = parts.slice(1);

    const captured = [];
    const oPrint = this.term.print.bind(this.term);
    const oPrintln = this.term.println.bind(this.term);
    if (redirOut || pipeMore) {
      this.term.print = s => { captured.push(s); };
      this.term.println = s => { captured.push((s || '') + '\n'); };
    }

    this._dispatch(name, args, line);

    if (redirOut || pipeMore) {
      this.term.print = oPrint; this.term.println = oPrintln;
      const txt = captured.join('');
      if (redirOut) {
        let content = txt;
        if (redirAppend) {
          const [dp, fn] = this._splitPath(redirOut);
          const old = this.disk.readFile([...this.cwdParts, ...dp], fn);
          if (old) content = new TextDecoder().decode(old) + txt;
        }
        const enc = new TextEncoder().encode(content);
        const [dp, fn] = this._splitPath(redirOut);
        try { this.disk.writeFile([...this.cwdParts, ...dp], fn, enc); this.disk.flush(); }
        catch (e) { this.term.println('Write error: ' + e.message); }
      }
      if (pipeMore) txt.split('\n').forEach(l => this.term.println(l));
    }

    // EDIT/COPY CON は非同期なのでpromptを出さない
    if (window._editInstance || window._copyConInstance) return;

    this.term.println('');
    this.prompt();
  }

  _dispatch(name, args, rawLine) {
    switch (name) {
      case 'CLS':    this.term.clear(); break;
      case 'VER':    this.term.println('MYDOS Version 1.0  Copyright (C) 2025'); break;
      case 'DIR':    this._dir(args); break;
      case 'CD': case 'CHDIR': this._cd(args); break;
      case 'MD': case 'MKDIR': this._md(args); break;
      case 'RD': case 'RMDIR': this._rd(args); break;
      case 'TYPE':   this._type(args); break;
      case 'COPY':   this._copy(args, rawLine); break;
      case 'XCOPY':  this._copy(args.filter(a => !a.startsWith('/')), rawLine); break;
      case 'DEL': case 'ERASE': this._del(args); break;
      case 'REN': case 'RENAME': this._ren(args); break;
      case 'MOVE':   this._move(args); break;
      case 'ECHO':   this._echo(args); break;
      case 'SET':    this._set(args); break;
      case 'PATH':   this._path(args); break;
      case 'PROMPT': this._promptCmd(args); break;
      case 'DATE':   this._date(args); break;
      case 'TIME':   this._time(args); break;
      case 'VOL':    this.term.println(' ドライブ A のボリュームラベルは MYDOS\n ボリュームシリアル番号は DEAD-BEEF'); break;
      case 'FORMAT': this._format(args); break;
      case 'CHKDSK': case 'SCANDISK': this._chkdsk(); break;
      case 'ATTRIB': this._attrib(args); break;
      case 'FIND': case 'FINDSTR': this._find(args); break;
      case 'MORE':   this._type(args); break;
      case 'SORT':   this._sort(args); break;
      case 'TREE':   this._tree(args); break;
      case 'MEM':    this._mem(); break;
      case 'EDIT':   this._edit(args); break;
      case 'DEBUG':  this._debug(args); break;
      case 'FC':     this._fc(args); break;
      case 'COMP':   this._fc(args); break;
      case 'DELTREE':this._deltree(args); break;
      case 'CHOICE': this._choice(args); break;
      case 'LABEL':  this.term.println('ボリュームラベル: MYDOS'); break;
      case 'PRINT':  this.term.println('プリンタが接続されていません'); break;
      case 'PAUSE':  this.term.println('続行するには何かキーを押してください...'); break;
      case 'REM':    break;
      case 'BREAK':  this.term.println('BREAK is OFF'); break;
      case 'VERIFY': this.term.println('VERIFY is OFF'); break;
      case 'TRUENAME': this.term.println(this.cwdStr()); break;
      case 'DISKCOMP': case 'DISKCOPY': this.term.println('このコマンドはサポートされていません'); break;
      case 'CALL':   this._call(args); break;
      case 'GOTO':   this.term.println('GOTOはバッチファイル専用です'); break;
      case 'IF':     this._if(args); break;
      case 'FOR':    this._for(args); break;
      case 'SHIFT':  this.term.println('SHIFTはバッチファイル専用です'); break;
      case 'EXIT':   this.term.println('DOSシェルを終了できません'); break;
      case 'DOSKEY': this.term.println('DOSKEY: コマンド履歴は有効です (↑↓キー)'); break;
      case 'MODE':   this.term.println('現在のモード: CON: COLS=80 LINES=25'); break;
      case 'START':  this.term.println('Windows は利用できません'); break;
      case 'COMMAND':this.term.println('MYDOS Version 1.0'); break;
      case 'SYS':    this.term.println('システムファイルを転送しました (stub)'); break;
      case 'SUBST':  this.term.println('SUBST: 仮想ドライブはサポートされていません'); break;
      case 'CHCP':   this.term.println('現在のコードページ: 932'); break;
      case 'HELP':   this._help(args); break;
      default:       this._runFile(name, args); break;
    }
  }

  // ── DIR ──
  _dir(args) {
    let tgt = [...this.cwdParts], wide = false, bare = false, showAll = false;
    const filtered = args.filter(a => {
      const u = a.toUpperCase();
      if (u === '/W') { wide = true; return false; }
      if (u === '/B') { bare = true; return false; }
      if (u === '/A' || u === '/AH' || u === '/AS') { showAll = true; return false; }
      if (u === '/P' || u === '/S' || u === '/O') return false;
      return true;
    });
    let wildcard = '';
    if (filtered.length) {
      const p = filtered[0];
      if (p.includes('*') || p.includes('?')) { wildcard = p.toUpperCase(); }
      else { const [dp] = this._splitPath(p); tgt = [...this.cwdParts, ...dp]; }
    }
    const entries = this.disk.listDir(tgt);
    if (!entries) { this.term.println('パスが見つかりません'); return; }
    let list = entries.filter(e => e.name !== '.' && e.name !== '..');
    if (wildcard) {
      const re = new RegExp('^' + wildcard.replace(/\./g, '\\.').replace(/\*/g, '.*').replace(/\?/g, '.') + '$', 'i');
      list = list.filter(e => re.test(e.name));
    }
    if (!bare) {
      this.term.println(` ドライブ A のボリュームラベルは MYDOS`);
      this.term.println(` ディレクトリ: ${this.cwdStr()}`);
      this.term.println('');
    }
    let totalFiles = 0, totalSize = 0;
    if (wide) {
      let line = '';
      list.forEach(e => {
        const isDir = e.attr & 0x10;
        const label = isDir ? `[${e.name}]` : e.name;
        line += label.padEnd(16);
        if (line.length >= 64) { this.term.println(line); line = ''; }
        if (!isDir) { totalFiles++; totalSize += e.size; }
      });
      if (line) this.term.println(line);
    } else {
      list.forEach(e => {
        const isDir = e.attr & 0x10;
        if (bare) {
          this.term.println(e.name);
        } else {
          const sz = isDir ? '<DIR>' : e.size.toString().padStart(10);
          this.term.println(`${e.name.padEnd(13)} ${sz}`);
        }
        if (!isDir) { totalFiles++; totalSize += e.size; }
      });
    }
    if (!bare) {
      this.term.println(`       ${totalFiles} 個のファイル    ${totalSize.toLocaleString()} バイト`);
      this.term.println(`                          ${(this.disk.freeClusters() * 512).toLocaleString()} バイトの空き領域`);
    }
  }

  // ── CD ──
  _cd(args) {
    if (!args[0]) { this.term.println(this.cwdStr()); return; }
    const target = args[0].replace(/^A:\\/i, '').replace(/\\/g, '/');
    if (target === '\\' || target === '/') { this.cwdParts = []; return; }
    const parts = target.split('/').filter(Boolean);
    let newParts = [...this.cwdParts];
    for (const p of parts) {
      if (p === '..') { newParts.pop(); }
      else if (p !== '.') { newParts.push(p.toUpperCase()); }
    }
    if (this.disk._resolveDirSectors(newParts)) { this.cwdParts = newParts; }
    else this.term.println('パスが見つかりません');
  }

  // ── MD ──
  _md(args) {
    if (!args[0]) { this.term.println('ディレクトリ名を指定してください'); return; }
    try { this.disk.mkdir(this.cwdParts, args[0].toUpperCase()); this.disk.flush(); }
    catch (e) { this.term.println(e.message); }
  }

  // ── RD ──
  _rd(args) {
    if (!args[0]) { this.term.println('ディレクトリ名を指定してください'); return; }
    const name = args[0].toUpperCase();
    const secs = this.disk._resolveDirSectors([...this.cwdParts, name]);
    if (!secs) { this.term.println('ディレクトリが見つかりません'); return; }
    const entries = this.disk._enumEntries(secs).filter(e => e.name !== '.' && e.name !== '..');
    if (entries.length) { this.term.println('ディレクトリが空ではありません'); return; }
    this.disk.deleteEntry(this.cwdParts, name);
  }

  // ── TYPE ──
  _type(args) {
    if (!args[0]) { this.term.println('ファイル名を指定してください'); return; }
    const [dp, fn] = this._splitPath(args[0]);
    const data = this.disk.readFile([...this.cwdParts, ...dp], fn);
    if (!data) { this.term.println(`ファイルが見つかりません - ${fn}`); return; }
    let line = '';
    for (let i = 0; i < data.length; i++) {
      const c = data[i]; if (c === 0x1A) break; if (c === 0x0D) continue;
      if (c === 0x0A) { this.term.println(line); line = ''; }
      else line += (c >= 0x20 && c < 0x7F) ? String.fromCharCode(c) : '.';
    }
    if (line) this.term.println(line);
  }

  // ── COPY (COPY CON 対応) ──
  _copy(args, rawLine) {
    if (!args[0]) { this.term.println('コピー元を指定してください'); return; }
    // COPY CON filename
    if (args[0].toUpperCase() === 'CON' && args[1]) {
      this._startCopyCon(args[1]);
      return;
    }
    const [sdp, sfn] = this._splitPath(args[0]);
    const data = this.disk.readFile([...this.cwdParts, ...sdp], sfn);
    if (!data) { this.term.println(`ファイルが見つかりません - ${sfn}`); return; }
    let dfn = sfn, dbase = [...this.cwdParts];
    if (args[1]) {
      if (args[1].toUpperCase() === 'CON') {
        // COPY file CON → TYPE と同じ
        let line = '';
        for (let i = 0; i < data.length; i++) {
          const c = data[i]; if (c === 0x1A) break; if (c === 0x0D) continue;
          if (c === 0x0A) { this.term.println(line); line = ''; }
          else line += (c >= 0x20 && c < 0x7F) ? String.fromCharCode(c) : '.';
        }
        if (line) this.term.println(line);
        return;
      }
      const [ddp, dfname] = this._splitPath(args[1]);
      dbase = [...this.cwdParts, ...ddp]; dfn = dfname || sfn;
    }
    try {
      this.disk.writeFile(dbase, dfn, data); this.disk.flush();
      this.term.println('        1 個のファイルをコピーしました');
    } catch (e) { this.term.println(e.message); }
  }

  _startCopyCon(filename) {
    const cc = new CopyCon(this.disk, [...this.cwdParts], this.term, filename);
    window._copyConInstance = cc;
    cc.onExit = () => {
      window._copyConInstance = null;
      this.term.println('');
      this.prompt();
    };
    cc.start();
  }

  // ── EDIT ──
  _edit(args) {
    const ed = new DosEdit(this.disk, [...this.cwdParts], this.term);
    window._editInstance = ed;
    ed.onExit = () => {
      window._editInstance = null;
      if (window._editExit) window._editExit();
      this.term.println('');
      this.prompt();
      if (window.onDiskChange) window.onDiskChange();
    };
    ed.open(args[0] || '');
  }

  // ── DEBUG (簡易hex dump) ──
  _debug(args) {
    if (!args[0]) { this.term.println('使用法: DEBUG ファイル名'); return; }
    const [dp, fn] = this._splitPath(args[0]);
    const data = this.disk.readFile([...this.cwdParts, ...dp], fn);
    if (!data) { this.term.println(`ファイルが見つかりません - ${fn}`); return; }
    this.term.println(`-d 0100`);
    for (let off = 0; off < Math.min(data.length, 256); off += 16) {
      let hex = '', ascii = '';
      for (let i = 0; i < 16; i++) {
        if (off + i < data.length) {
          const b = data[off + i];
          hex += b.toString(16).padStart(2, '0').toUpperCase() + ' ';
          ascii += (b >= 0x20 && b < 0x7F) ? String.fromCharCode(b) : '.';
        } else { hex += '   '; ascii += ' '; }
        if (i === 7) hex += ' ';
      }
      this.term.println(`${(0x100 + off).toString(16).padStart(4, '0').toUpperCase()}  ${hex} ${ascii}`);
    }
    this.term.println('-q');
  }

  // ── FC (ファイル比較) ──
  _fc(args) {
    if (args.length < 2) { this.term.println('使用法: FC ファイル1 ファイル2'); return; }
    const [dp1, fn1] = this._splitPath(args[0]);
    const [dp2, fn2] = this._splitPath(args[1]);
    const d1 = this.disk.readFile([...this.cwdParts, ...dp1], fn1);
    const d2 = this.disk.readFile([...this.cwdParts, ...dp2], fn2);
    if (!d1) { this.term.println(`ファイルが見つかりません - ${fn1}`); return; }
    if (!d2) { this.term.println(`ファイルが見つかりません - ${fn2}`); return; }
    const t1 = new TextDecoder().decode(d1).split('\n');
    const t2 = new TextDecoder().decode(d2).split('\n');
    let diffs = 0;
    const maxL = Math.max(t1.length, t2.length);
    for (let i = 0; i < maxL; i++) {
      const l1 = (t1[i] || '').trimEnd();
      const l2 = (t2[i] || '').trimEnd();
      if (l1 !== l2) {
        if (diffs === 0) this.term.println(`***** ${fn1} と ${fn2} の比較`);
        this.term.println(`行${i + 1}:`);
        this.term.println(`< ${l1}`);
        this.term.println(`> ${l2}`);
        diffs++;
      }
    }
    if (diffs === 0) this.term.println('FC: 相違点はありません');
    else this.term.println(`\n${diffs} 箇所の相違が見つかりました`);
  }

  // ── DELTREE ──
  _deltree(args) {
    if (!args[0]) { this.term.println('使用法: DELTREE ディレクトリ名'); return; }
    const name = args[0].toUpperCase();
    // ファイルの場合は普通に削除
    const entries = this.disk.listDir(this.cwdParts) || [];
    const target = entries.find(e => e.name.toUpperCase() === name);
    if (!target) { this.term.println('パスが見つかりません'); return; }
    if (!(target.attr & 0x10)) {
      this.disk.deleteEntry(this.cwdParts, name);
      this.term.println(`${name} を削除しました`);
      return;
    }
    // ディレクトリ内を再帰削除
    this._deltreeRec([...this.cwdParts, name]);
    this.disk.deleteEntry(this.cwdParts, name);
    this.disk.flush();
    this.term.println(`${name} ツリーを削除しました`);
  }

  _deltreeRec(parts) {
    const entries = (this.disk.listDir(parts) || []).filter(e => e.name !== '.' && e.name !== '..');
    for (const e of entries) {
      if (e.attr & 0x10) { this._deltreeRec([...parts, e.name]); }
      this.disk.deleteEntry(parts, e.name);
    }
  }

  // ── CHOICE ──
  _choice(args) {
    this.term.println('[Y,N]? (Y)');
    // 簡易: 常にYを返す
  }

  // ── DATE / TIME ──
  _date(args) {
    const now = new Date();
    this.term.println(`現在の日付: ${now.getFullYear()}/${String(now.getMonth()+1).padStart(2,'0')}/${String(now.getDate()).padStart(2,'0')}`);
  }
  _time(args) {
    const now = new Date();
    this.term.println(`現在の時刻: ${String(now.getHours()).padStart(2,'0')}:${String(now.getMinutes()).padStart(2,'0')}:${String(now.getSeconds()).padStart(2,'0')}`);
  }

  _del(args) {
    if (!args[0]) { this.term.println('ファイル名を指定してください'); return; }
    const t = args[0];
    if (t === '*.*' || t === '*') {
      const ent = this.disk.listDir(this.cwdParts) || [];
      let cnt = 0;
      for (const e of ent) if (!(e.attr & 0x10)) { this.disk.deleteEntry(this.cwdParts, e.name); cnt++; }
      this.disk.flush(); this.term.println(`${cnt} 個のファイルを削除しました`); return;
    }
    // Wildcard delete
    if (t.includes('*') || t.includes('?')) {
      const re = new RegExp('^' + t.toUpperCase().replace(/\./g, '\\.').replace(/\*/g, '.*').replace(/\?/g, '.') + '$', 'i');
      const ent = (this.disk.listDir(this.cwdParts) || []).filter(e => !(e.attr & 0x10) && re.test(e.name));
      ent.forEach(e => this.disk.deleteEntry(this.cwdParts, e.name));
      this.disk.flush();
      this.term.println(`${ent.length} 個のファイルを削除しました`);
      return;
    }
    const [dp, fn] = this._splitPath(t);
    if (this.disk.deleteEntry([...this.cwdParts, ...dp], fn)) this.disk.flush();
    else this.term.println(`ファイルが見つかりません - ${fn}`);
  }

  _ren(args) {
    if (args.length < 2) { this.term.println('ファイル名を2つ指定してください'); return; }
    const [dp, on] = this._splitPath(args[0]);
    if (this.disk.renameEntry([...this.cwdParts, ...dp], on, args[1].toUpperCase())) this.disk.flush();
    else this.term.println(`ファイルが見つかりません - ${on}`);
  }

  _move(args) {
    if (args.length < 2) { this.term.println('移動元と移動先を指定してください'); return; }
    const [sdp, sfn] = this._splitPath(args[0]);
    const [ddp, dfn] = this._splitPath(args[1]);
    const data = this.disk.readFile([...this.cwdParts, ...sdp], sfn);
    if (!data) { this.term.println(`ファイルが見つかりません - ${sfn}`); return; }
    try {
      this.disk.writeFile([...this.cwdParts, ...ddp], dfn || sfn, data);
      this.disk.deleteEntry([...this.cwdParts, ...sdp], sfn);
      this.disk.flush(); this.term.println(`${sfn} を移動しました`);
    } catch (e) { this.term.println(e.message); }
  }

  _echo(args) {
    if (!args.length) { this.term.println(`ECHO is ${this.echoOn ? 'ON' : 'OFF'}`); return; }
    if (args[0].toUpperCase() === 'ON') { this.echoOn = true; return; }
    if (args[0].toUpperCase() === 'OFF') { this.echoOn = false; return; }
    if (args[0] === '.') { this.term.println(''); return; }
    this.term.println(args.join(' '));
  }

  _set(args) {
    if (!args.length) { for (const [k, v] of Object.entries(this.env)) this.term.println(`${k}=${v}`); return; }
    const full = args.join(' '), eq = full.indexOf('=');
    if (eq >= 0) { const k = full.slice(0, eq).toUpperCase(), v = full.slice(eq + 1); if (v) this.env[k] = v; else delete this.env[k]; }
    else { const k = full.toUpperCase(); this.term.println(this.env[k] !== undefined ? `${k}=${this.env[k]}` : `環境変数 ${k} は定義されていません`); }
  }

  _path(args) {
    if (!args[0]) { this.term.println('PATH=' + this.env.PATH); return; }
    this.env.PATH = args.join(' ');
  }

  _promptCmd(args) {
    if (!args[0]) { this.term.println('PROMPT=' + this.env.PROMPT); return; }
    this.env.PROMPT = args.join(' ');
  }

  _format(args) {
    if (!args.some(a => a.toUpperCase() === '/Y')) {
      this.term.println('警告: すべてのデータが失われます！');
      this.term.println('フォーマットするには FORMAT /Y を使用してください');
      return;
    }
    this.disk.format(); this.cwdParts = [];
    this.term.println('フォーマット完了\n1,457,664 バイト  使用可能');
  }

  _chkdsk() {
    const free = this.disk.freeClusters();
    const max = Math.floor(this.disk.SECTORS_PER_FAT * 512 * 2 / 3) - 2;
    this.term.println(` 1,457,664 バイト  総ディスク領域`);
    this.term.println(`   ${((max - free) * 512).toLocaleString()} バイト  使用済み`);
    this.term.println(`   ${(free * 512).toLocaleString()} バイト  使用可能`);
    this.term.println('\n   655,360 バイト  総メモリ\n   655,360 バイト  使用可能');
  }

  _attrib(args) {
    const entries = this.disk.listDir(this.cwdParts) || [];
    for (const e of entries) {
      const a = e.attr;
      this.term.println([(a & 0x20 ? 'A' : ' '), (a & 0x02 ? 'H' : ' '), (a & 0x01 ? 'R' : ' '), (a & 0x04 ? 'S' : ' ')].join('') + `  A:\\${[...this.cwdParts, e.name].join('\\')}`);
    }
  }

  _find(args) {
    const q = args.find(a => a.startsWith('"') && a.endsWith('"'));
    if (!q) { this.term.println('使用法: FIND "文字列" [ファイル名]'); return; }
    const needle = q.slice(1, -1).toLowerCase();
    const fileArg = args.find(a => !a.startsWith('"') && !a.startsWith('/'));
    const entries = fileArg ? [{ name: fileArg }] : (this.disk.listDir(this.cwdParts) || []).filter(e => !(e.attr & 0x10));
    for (const e of entries) {
      const [dp, fn] = this._splitPath(e.name);
      const data = this.disk.readFile([...this.cwdParts, ...dp], fn);
      if (!data) continue;
      const text = new TextDecoder().decode(data);
      let found = false;
      text.split('\n').forEach(l => {
        if (l.toLowerCase().includes(needle)) {
          if (!found) { this.term.println(`---------- ${fn}`); found = true; }
          this.term.println(l);
        }
      });
    }
  }

  _sort(args) {
    if (!args[0]) { this.term.println('使用法: SORT ファイル名'); return; }
    const [dp, fn] = this._splitPath(args[0]);
    const data = this.disk.readFile([...this.cwdParts, ...dp], fn);
    if (!data) { this.term.println('ファイルが見つかりません'); return; }
    new TextDecoder().decode(data).split('\n').sort().forEach(l => this.term.println(l));
  }

  _tree(args) {
    this.term.println('A:\\' + this.cwdParts.join('\\'));
    this._treeRec(this.cwdParts, '');
  }

  _treeRec(parts, pfx) {
    const dirs = (this.disk.listDir(parts) || []).filter(e => (e.attr & 0x10) && e.name !== '.' && e.name !== '..');
    dirs.forEach((d, i) => {
      const last = i === dirs.length - 1;
      this.term.println(`${pfx}${last ? '└' : '├'}── ${d.name}`);
      this._treeRec([...parts, d.name], pfx + (last ? '    ' : '│   '));
    });
  }

  _mem() {
    this.term.println('メモリタイプ             合計      使用済み      空き');
    this.term.println('------------------- -------- ------------ --------');
    this.term.println('通常メモリ            655,360            0   655,360');
    this.term.println('上位メモリ                  0            0         0');
    this.term.println('');
    this.term.println('合計メモリ            655,360            0   655,360');
    this.term.println('');
    this.term.println('最大の実行可能プログラム サイズ: 655,360 (640K)');
  }

  _if(args) {
    const raw = args.join(' ');
    const m = raw.match(/^EXIST\s+(\S+)\s+(.+)$/i);
    if (m) {
      const [dp, fn] = this._splitPath(m[1]);
      const exists = !!this.disk.readFile([...this.cwdParts, ...dp], fn);
      if (exists) { const p = this._splitArgs(m[2]); this._dispatch(p[0].toUpperCase(), p.slice(1), m[2]); }
      return;
    }
    const mn = raw.match(/^NOT\s+EXIST\s+(\S+)\s+(.+)$/i);
    if (mn) {
      const [dp, fn] = this._splitPath(mn[1]);
      const exists = !!this.disk.readFile([...this.cwdParts, ...dp], fn);
      if (!exists) { const p = this._splitArgs(mn[2]); this._dispatch(p[0].toUpperCase(), p.slice(1), mn[2]); }
      return;
    }
    // IF string1==string2 command
    const eq = raw.match(/^"?([^"=]*)"?\s*==\s*"?([^"]*)"?\s+(.+)$/);
    if (eq) {
      if (eq[1].trim() === eq[2].trim()) { const p = this._splitArgs(eq[3]); this._dispatch(p[0].toUpperCase(), p.slice(1), eq[3]); }
      return;
    }
    // IF ERRORLEVEL n command
    const el = raw.match(/^ERRORLEVEL\s+(\d+)\s+(.+)$/i);
    if (el) {
      // Always 0 for now
      if (0 >= parseInt(el[1])) { const p = this._splitArgs(el[2]); this._dispatch(p[0].toUpperCase(), p.slice(1), el[2]); }
      return;
    }
  }

  _for(args) {
    // FOR %x IN (set) DO command
    const raw = args.join(' ');
    const m = raw.match(/^%(\w)\s+IN\s+\(([^)]+)\)\s+DO\s+(.+)$/i);
    if (!m) { this.term.println('使用法: FOR %x IN (セット) DO コマンド'); return; }
    const varName = m[1], items = m[2].split(/\s+/), cmdTpl = m[3];
    for (const item of items) {
      const cmd = cmdTpl.replace(new RegExp('%' + varName, 'gi'), item);
      const p = this._splitArgs(cmd);
      this._dispatch(p[0].toUpperCase(), p.slice(1), cmd);
    }
  }

  _call(args) {
    if (!args[0]) { this.term.println('使用法: CALL バッチファイル'); return; }
    const fn = args[0].toUpperCase();
    const name = fn.includes('.') ? fn : fn + '.BAT';
    const data = this.disk.readFile(this.cwdParts, name);
    if (!data) { this.term.println(`バッチファイルが見つかりません - ${name}`); return; }
    const lines = new TextDecoder().decode(data).split('\n').map(l => l.trim()).filter(l => l);
    for (const l of lines) {
      if (l.toUpperCase().startsWith('REM') || l.startsWith(':')) continue;
      const p = this._splitArgs(l); if (p[0]) this._dispatch(p[0].toUpperCase(), p.slice(1), l);
    }
  }

  _help(args) {
    if (args[0]) {
      const h = this._helpDetail(args[0].toUpperCase());
      this.term.println(h);
      return;
    }
    const cmds = [
      ['ATTRIB',  'ファイル属性の表示/変更'],
      ['CALL',    'バッチファイルの呼び出し'],
      ['CD',      'ディレクトリの変更'],
      ['CHKDSK',  'ディスクの状態をチェック'],
      ['CLS',     '画面のクリア'],
      ['COPY',    'ファイルのコピー (COPY CON対応)'],
      ['DATE',    '日付の表示'],
      ['DEBUG',   'ファイルのHEXダンプ表示'],
      ['DEL',     'ファイルの削除'],
      ['DELTREE', 'ディレクトリツリーの削除'],
      ['DIR',     'ディレクトリの一覧表示'],
      ['ECHO',    'メッセージの表示'],
      ['EDIT',    'テキストエディタ'],
      ['FC',      'ファイルの比較'],
      ['FIND',    'ファイル内の文字列検索'],
      ['FOR',     'ループ実行'],
      ['FORMAT',  'ディスクのフォーマット'],
      ['HELP',    'ヘルプの表示'],
      ['IF',      '条件処理'],
      ['MD',      'ディレクトリの作成'],
      ['MEM',     'メモリの表示'],
      ['MORE',    'ファイルの表示'],
      ['MOVE',    'ファイルの移動'],
      ['PATH',    'パスの設定'],
      ['PAUSE',   '処理の一時停止'],
      ['PROMPT',  'プロンプトの変更'],
      ['RD',      'ディレクトリの削除'],
      ['REN',     'ファイル名の変更'],
      ['SET',     '環境変数の設定'],
      ['SORT',    'ファイルのソート表示'],
      ['TIME',    '時刻の表示'],
      ['TREE',    'ディレクトリツリーの表示'],
      ['TYPE',    'ファイル内容の表示'],
      ['VER',     'バージョン情報の表示'],
      ['VOL',     'ボリューム情報の表示'],
    ];
    this.term.println('コマンドの一覧:');
    this.term.println('');
    cmds.forEach(([n, d]) => this.term.println(`  ${n.padEnd(10)} ${d}`));
    this.term.println('');
    this.term.println('HELP コマンド名 で詳細を表示');
  }

  _helpDetail(cmd) {
    const h = {
      'COPY':  'COPY 元 先\nCOPY CON ファイル名  (コンソールからファイル作成、Ctrl+Zで保存)\nCOPY ファイル CON    (ファイル内容を表示)',
      'EDIT':  'EDIT [ファイル名]\nフルスクリーンテキストエディタを起動\n  Ctrl+S: 保存  Ctrl+Q: 終了  Ctrl+N: 新規\n  Esc: 終了  F1: ヘルプ',
      'DIR':   'DIR [パス] [/W] [/B] [/A]\n  /W  ワイド表示  /B  ファイル名のみ',
      'DEL':   'DEL ファイル名\nワイルドカード(*.*)使用可',
      'DEBUG': 'DEBUG ファイル名\nファイルの16進ダンプを表示',
      'FC':    'FC ファイル1 ファイル2\n2つのテキストファイルを比較',
      'FOR':   'FOR %x IN (セット) DO コマンド',
      'IF':    'IF EXIST ファイル コマンド\nIF NOT EXIST ファイル コマンド\nIF 文字列1==文字列2 コマンド',
      'ECHO':  'ECHO [メッセージ]\nECHO.  (空行を出力)\nECHO ON/OFF',
    };
    return h[cmd] || `${cmd} のヘルプは準備中です`;
  }

  // ── BATファイル実行 + .COM実行 ──
  _runFile(name, args) {
    for (const fn of [name + '.COM', name + '.EXE', name + '.BAT', name]) {
      const data = this.disk.readFile(this.cwdParts, fn);
      if (data) {
        if (fn.endsWith('.BAT')) {
          this._runBat(fn, data, args);
          return;
        }
        if (typeof CPU8086 !== 'undefined' && typeof Memory !== 'undefined') {
          this._execCOM(fn, data);
        } else {
          this.term.println(`[${fn} - ${data.length}B - cpu8086.jsが必要です]`);
        }
        return;
      }
    }
    this.term.println(`'${name}' は内部コマンドでも外部コマンドでもありません`);
  }

  _runBat(fn, data, args) {
    const lines = new TextDecoder().decode(data).split('\n').map(l => l.trim());
    const labels = {};
    // First pass: find labels
    lines.forEach((l, i) => { if (l.startsWith(':')) labels[l.slice(1).trim().toUpperCase()] = i; });
    // Execute
    let ip = 0;
    while (ip < lines.length) {
      let l = lines[ip]; ip++;
      if (!l || l.startsWith(':')) continue;
      // Replace %1-%9 with args
      for (let i = 0; i < 9; i++) {
        l = l.replace(new RegExp('%' + (i + 1), 'g'), args[i] || '');
      }
      l = l.replace(/%0/g, fn);
      if (l.startsWith('@')) l = l.slice(1).trim();
      const p = this._splitArgs(l);
      const cmd = (p[0] || '').toUpperCase();
      if (cmd === 'GOTO') {
        const target = (p[1] || '').toUpperCase();
        if (labels[target] !== undefined) ip = labels[target] + 1;
        continue;
      }
      if (cmd === 'IF') {
        // Inline IF handling for batch
        this._if(p.slice(1));
        continue;
      }
      if (cmd === 'CALL') {
        this._call(p.slice(1));
        continue;
      }
      if (p[0]) this._dispatch(cmd, p.slice(1), l);
    }
  }

  _execCOM(fn, data) {
    if (window._cpuRunning) { this.term.println('既に実行中です'); return; }
    this.term.println('実行: ' + fn + ' (' + data.length + 'B)');
    try {
      const mem = new Memory();
      const cpu = new CPU8086(mem);
      cpu.installBIOS();
      const ORG = 0x0100;
      mem.load(ORG, data);
      cpu.reg.cs = 0; cpu.reg.ds = 0; cpu.reg.es = 0; cpu.reg.ss = 0;
      cpu.reg.sp = 0xFFFE; cpu.reg.ip = ORG;
      const term = this.term;
      const shell = this;
      window._cpuInstance = cpu;
      window._cpuMem = mem;
      window._cpuRunning = true;
      cpu.onBiosOutput = () => {};
      const CYCLES_PER_TICK = 100000;
      const tick = () => {
        if (!window._cpuRunning) return;
        const t0 = performance.now();
        let ran = 0;
        while (ran < CYCLES_PER_TICK) {
          if (cpu.halted) break;
          cpu.step(); ran++;
          if (performance.now() - t0 > 14) break;
        }
        if (window.renderVRAM) window.renderVRAM();
        if (cpu.halted) {
          const physIP = (cpu.reg.cs * 16 + cpu.reg.ip) & 0xFFFFF;
          const op = mem.read8(physIP);
          if (op === 0xF4) {
            window._cpuRunning = false;
            window._cpuInstance = null;
            window._cpuMem = null;
            if (window.exitVRAMMode) window.exitVRAMMode();
            term.println('');
            shell.prompt();
            if (window.onDiskChange) window.onDiskChange();
            return;
          }
        }
        requestAnimationFrame(tick);
      };
      tick();
    } catch (e) {
      this.term.println('実行エラー: ' + e.message);
      window._cpuRunning = false;
    }
  }

  _splitPath(p) {
    p = (p || '').replace(/^A:\\/i, '').replace(/\\/g, '/');
    const parts = p.split('/').filter(Boolean);
    if (!parts.length) return [[], ''];
    const fn = parts.pop().toUpperCase();
    return [parts.map(s => s.toUpperCase()), fn];
  }

  _splitArgs(line) {
    const a = []; let cur = '', inQ = false;
    for (const c of line) {
      if (c === '"') { inQ = !inQ; continue; }
      if (c === ' ' && !inQ) { if (cur) { a.push(cur); cur = ''; } } else cur += c;
    }
    if (cur) a.push(cur); return a;
  }
}

// ============================================================
// ターミナル (デフォルト実装)
// ============================================================
class Terminal {
  constructor(el) { this.el = el; this.buf = ''; this.MAX = 80000; }
  print(s) { this.buf += s; this._flush(); }
  println(s = '') { this.buf += (s || '') + '\n'; this._flush(); }
  clear() { this.buf = ''; this.el.textContent = ''; }
  _flush() {
    if (this.buf.length > this.MAX) this.buf = this.buf.slice(-this.MAX);
    this.el.textContent = this.buf;
    this.el.scrollTop = this.el.scrollHeight;
  }
}

// ============================================================
// 公開API
// ============================================================
window.MSDos = {
  disk: null, shell: null, term: null,

  init(outputEl, inputEl) {
    this.term = new Terminal(outputEl);
    this.disk = new FAT12Disk();
    if (!this.disk.isFormatted()) {
      this.disk.format();
      this.term.println('[新しいディスクをフォーマットしました]');
    } else {
      this.term.println('[ディスクをlocalStorageから読み込みました]');
    }
    this.shell = new DOSShell(this.disk, this.term);
    this.shell.start();

    inputEl.addEventListener('keydown', e => {
      if (e.key === 'Enter') {
        const line = inputEl.value;
        this.term.print(line);
        inputEl.value = '';
        this.shell.execute(line);
        if (window.onDiskChange) window.onDiskChange();
      }
    });
  },

  saveCom(name, bytes) {
    try { this.disk.writeFile([], name, new Uint8Array(bytes)); this.disk.flush(); if (window.onDiskChange) window.onDiskChange(); return true; }
    catch (e) { return e.message; }
  },

  importFile(name, bytes) { return this.saveCom(name.toUpperCase(), bytes); },
  downloadImg() { this.disk.download('disk.img'); },

  format() {
    this.disk.format(); this.shell.cwdParts = [];
    this.term.println('[ディスクをフォーマットしました]');
    if (window.onDiskChange) window.onDiskChange();
  },

  getFiles() { return this.disk ? this.disk.listDir([]) || [] : []; }
};