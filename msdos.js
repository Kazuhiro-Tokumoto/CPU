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

  // ---- セクタキャッシュ ----
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

  isFormatted() { return this.r8(0,510)===0x55&&this.r8(0,511)===0xAA; }

  format(label='MYDOS      ') {
    this.wipeStorage();
    // BPB
    const s0=this._sec(0); s0.fill(0);
    s0[0]=0xEB;s0[1]=0x3C;s0[2]=0x90;
    const oem='MYDOS   ';
    for(let i=0;i<8;i++) s0[3+i]=oem.charCodeAt(i);
    this.w16(0,11,512); this.w8(0,13,1); this.w16(0,14,1); this.w8(0,16,2);
    this.w16(0,17,224); this.w16(0,19,2880); this.w8(0,21,0xF0);
    this.w16(0,22,9); this.w16(0,24,18); this.w16(0,26,2);
    this.w32(0,28,0); this.w32(0,32,0);
    this.w8(0,36,0); this.w8(0,37,0); this.w8(0,38,0x29);
    this.w32(0,39,0xDEADBEEF);
    const lb=(label+'           ').slice(0,11);
    for(let i=0;i<11;i++) this.w8(0,43+i,lb.charCodeAt(i));
    const fs='FAT12   ';
    for(let i=0;i<8;i++) this.w8(0,54+i,fs.charCodeAt(i));
    this.w8(0,510,0x55); this.w8(0,511,0xAA);
    this._dirty.add(0);
    // FAT
    for(const fs of [this.FAT1_START,this.FAT2_START]) {
      const s=this._sec(fs); s.fill(0);
      s[0]=0xF0;s[1]=0xFF;s[2]=0xFF;
      this._dirty.add(fs);
    }
    this.flush();
  }

  // ---- FAT12 ----
  getFAT(c) {
    const bo=Math.floor(c*3/2);
    const sn=this.FAT1_START+Math.floor(bo/512), so=bo%512;
    const sn2=this.FAT1_START+Math.floor((bo+1)/512), so2=(bo+1)%512;
    const val=this.r8(sn,so)|(this.r8(sn2,so2)<<8);
    return (c&1)?(val>>4):(val&0xFFF);
  }

  setFAT(c,v) {
    for(const fs of [this.FAT1_START,this.FAT2_START]) {
      const bo=Math.floor(c*3/2);
      const sn=fs+Math.floor(bo/512),so=bo%512;
      const sn2=fs+Math.floor((bo+1)/512),so2=(bo+1)%512;
      if(c&1){
        this.w8(sn,so,(this.r8(sn,so)&0x0F)|((v&0xF)<<4));
        this.w8(sn2,so2,(v>>4)&0xFF);
      } else {
        this.w8(sn,so,v&0xFF);
        this.w8(sn2,so2,(this.r8(sn2,so2)&0xF0)|((v>>8)&0xF));
      }
    }
  }

  allocCluster() {
    const max=Math.floor(this.SECTORS_PER_FAT*512*2/3);
    for(let c=2;c<max;c++) if(this.getFAT(c)===0) return c;
    return -1;
  }

  freeChain(c) {
    while(c>=2&&c<0xFF8){const n=this.getFAT(c);this.setFAT(c,0);c=n;}
  }

  c2s(c) { return this.DATA_START+(c-2)*this.SECTORS_PER_CLUSTER; }

  // ---- ディレクトリ ----
  _rootSectors() {
    const a=[];for(let i=0;i<this.ROOT_SECTORS;i++) a.push(this.ROOT_START+i);return a;
  }

  _chainSectors(c) {
    const a=[];
    while(c>=2&&c<0xFF8){a.push(this.c2s(c));c=this.getFAT(c);}
    return a;
  }

  _resolveDirSectors(parts) {
    let sectors=this._rootSectors();
    for(const p of parts) {
      if(!p) continue;
      const e=this._enumEntries(sectors).find(e=>(e.attr&0x10)&&e.name.toUpperCase()===p.toUpperCase());
      if(!e) return null;
      sectors=this._chainSectors(e.cluster);
    }
    return sectors;
  }

  _enumEntries(sectors) {
    const res=[];
    for(const sec of sectors) {
      for(let slot=0;slot<16;slot++) {
        const off=slot*32;
        const first=this.r8(sec,off);
        if(first===0x00) return res;
        if(first===0xE5) continue;
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

  // ---- 公開API ----
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
    this.w16(sec,eoff+26,first<0?0:first);
    this.w32(sec,eoff+28,data.length);
    this._dirty.add(sec);
  }

  mkdir(parts,name) {
    const parentSecs=this._resolveDirSectors(parts);
    if(!parentSecs) throw new Error('Parent not found');
    if(this._enumEntries(parentSecs).find(e=>(e.attr&0x10)&&e.name.toUpperCase()===name.toUpperCase()))
      throw new Error('Already exists');
    const c=this.allocCluster();
    if(c<0) throw new Error('Disk full');
    this.setFAT(c,0xFFF);
    const sec=this.c2s(c);
    for(let i=0;i<512;i++) this.w8(sec,i,0);
    // . entry
    for(let i=0;i<11;i++) this.w8(sec,i,'.          '.charCodeAt(i));
    this.w8(sec,11,0x10); this.w16(sec,26,c);
    // .. entry
    for(let i=0;i<11;i++) this.w8(sec,32+i,'..         '.charCodeAt(i));
    this.w8(sec,43,0x10); this.w16(sec,58,0);
    this._dirty.add(sec);
    const {sec:ps,slot}=this._allocEntry(parentSecs);
    if(ps<0) throw new Error('Directory full');
    const off=slot*32;
    for(let i=0;i<32;i++) this.w8(ps,off+i,0);
    this._writeName83(ps,off,name);
    this.w8(ps,off+11,0x10);
    this.w16(ps,off+26,c);
    this.w32(ps,off+28,0);
    this._dirty.add(ps);
  }

  deleteEntry(parts,name) {
    const secs=this._resolveDirSectors(parts);
    if(!secs) return false;
    for(const sec of secs) {
      for(let slot=0;slot<16;slot++) {
        const e=this._readEntry(sec,slot);
        if(e.first===0x00) return false;
        if(e.first===0xE5) continue;
        if(e.name.toUpperCase()===name.toUpperCase()) {
          if(e.cluster>=2) this.freeChain(e.cluster);
          this.w8(sec,slot*32,0xE5);
          this._dirty.add(sec);
          return true;
        }
      }
    }
    return false;
  }

  renameEntry(parts,oldName,newName) {
    const secs=this._resolveDirSectors(parts);
    if(!secs) return false;
    for(const sec of secs) {
      for(let slot=0;slot<16;slot++) {
        const e=this._readEntry(sec,slot);
        if(e.first===0x00) return false;
        if(e.first===0xE5) continue;
        if(e.name.toUpperCase()===oldName.toUpperCase()) {
          this._writeName83(sec,slot*32,newName);
          this._dirty.add(sec);
          return true;
        }
      }
    }
    return false;
  }

  freeClusters() {
    const max=Math.floor(this.SECTORS_PER_FAT*512*2/3);
    let free=0;for(let c=2;c<max;c++) if(this.getFAT(c)===0)free++;return free;
  }

  toUint8Array() {
    const buf=new Uint8Array(this.TOTAL_SECTORS*512);
    for(let n=0;n<this.TOTAL_SECTORS;n++) buf.set(this._sec(n),n*512);
    return buf;
  }

  download(fn='disk.img') {
    const blob=new Blob([this.toUint8Array()],{type:'application/octet-stream'});
    const url=URL.createObjectURL(blob);
    const a=document.createElement('a');
    a.href=url;a.download=fn;a.click();URL.revokeObjectURL(url);
  }
}

// ============================================================
// DOSシェル
// ============================================================
class DOSShell {
  constructor(disk,term) {
    this.disk=disk; this.term=term;
    this.cwdParts=[];
    this.env={PATH:'A:\\',COMSPEC:'A:\\COMMAND.COM',PROMPT:'$P$G',TEMP:'A:\\TEMP'};
    this.history=[]; this.histIdx=-1;
  }

  cwdStr() { return 'A:\\'+this.cwdParts.join('\\')+( this.cwdParts.length?'\\':''); }

  prompt() {
    let p=this.env.PROMPT||'$P$G';
    const now=new Date();
    p=p.replace(/\$P/gi,this.cwdStr()).replace(/\$G/gi,'>').replace(/\$N/gi,'A')
       .replace(/\$D/gi,now.toLocaleDateString()).replace(/\$T/gi,now.toLocaleTimeString())
       .replace(/\$V/gi,'MYDOS 1.0').replace(/\$\$/gi,'$').replace(/\$_/gi,'\n');
    this.term.print(p);
  }

  start() {
    this.term.println('MYDOS Version 1.0');
    this.term.println('Copyright (C) 2025 MyDOS Systems');
    this.term.println('');
    this.prompt();
  }

  execute(line) {
    line=line.trim();
    if(!line){this.term.println('');this.prompt();return;}
    if(line.startsWith('@')) line=line.slice(1).trim();
    this.history.unshift(line); this.histIdx=-1;
    this.term.println('');

    // リダイレクト / パイプ
    let pipeMore=false, redirOut=null, cmd=line;
    const pm=line.match(/^(.*?)\s*\|\s*MORE\s*$/i);
    if(pm){pipeMore=true;cmd=pm[1].trim();}
    const rm=cmd.match(/^(.*?)\s*>\s*(\S+)\s*$/);
    if(rm){redirOut=rm[2];cmd=rm[1].trim();}

    const parts=this._splitArgs(cmd);
    const name=(parts[0]||'').toUpperCase();
    const args=parts.slice(1);

    const captured=[];
    const oPrint=this.term.print.bind(this.term);
    const oPrintln=this.term.println.bind(this.term);
    if(redirOut||pipeMore){
      this.term.print=s=>{captured.push(s);};
      this.term.println=s=>{captured.push((s||'')+'\n');};
    }

    this._dispatch(name,args);

    if(redirOut||pipeMore){
      this.term.print=oPrint; this.term.println=oPrintln;
      const txt=captured.join('');
      if(redirOut){
        const enc=new TextEncoder().encode(txt);
        const[dp,fn]=this._splitPath(redirOut);
        try{this.disk.writeFile([...this.cwdParts,...dp],fn,enc);this.disk.flush();}
        catch(e){this.term.println('Write error: '+e.message);}
      }
      if(pipeMore) txt.split('\n').forEach(l=>this.term.println(l));
    }

    this.term.println('');
    this.prompt();
  }

  _dispatch(name,args) {
    switch(name){
      case 'CLS':    this.term.clear();break;
      case 'VER':    this.term.println('MYDOS Version 1.0  Copyright (C) 2025');break;
      case 'DIR':    this._dir(args);break;
      case 'CD': case 'CHDIR': this._cd(args);break;
      case 'MD': case 'MKDIR': this._md(args);break;
      case 'RD': case 'RMDIR': this._rd(args);break;
      case 'TYPE':   this._type(args);break;
      case 'COPY':   this._copy(args);break;
      case 'XCOPY':  this._xcopy(args);break;
      case 'DEL': case 'ERASE': this._del(args);break;
      case 'REN': case 'RENAME': this._ren(args);break;
      case 'MOVE':   this._move(args);break;
      case 'ECHO':   this._echo(args);break;
      case 'SET':    this._set(args);break;
      case 'PATH':   this._path(args);break;
      case 'PROMPT': this._promptCmd(args);break;
      case 'DATE':   this.term.println('現在の日付: '+new Date().toLocaleDateString());break;
      case 'TIME':   this.term.println('現在の時刻: '+new Date().toLocaleTimeString());break;
      case 'VOL':    this.term.println(' ドライブ A のボリュームラベルは MYDOS\n ボリュームシリアル番号は DEAD-BEEF');break;
      case 'FORMAT': this._format(args);break;
      case 'CHKDSK': this._chkdsk();break;
      case 'ATTRIB': this._attrib(args);break;
      case 'FIND': case 'FINDSTR': this._find(args);break;
      case 'MORE':   this._type(args);break;
      case 'SORT':   this._sort(args);break;
      case 'TREE':   this._tree(args);break;
      case 'MEM':    this._mem();break;
      case 'LABEL':  this.term.println('[LABEL] 未サポート');break;
      case 'PRINT':  this.term.println('[PRINT] プリンタ未サポート');break;
      case 'DEBUG':  this.term.println('[DEBUG] 未実装');break;
      case 'EDIT':   this.term.println('[EDIT] index.htmlのエディタをご利用ください');break;
      case 'PAUSE':  this.term.println('続行するには何かキーを押してください...');break;
      case 'REM':    break;
      case 'BREAK':  this.term.println('^C');break;
      case 'VERIFY': this.term.println('VERIFY is OFF');break;
      case 'DISKCOMP':case 'DISKCOPY': this.term.println('このコマンドはサポートされていません');break;
      case 'CALL':   this.term.println('CALL: '+args.join(' '));break;
      case 'GOTO':   this.term.println('GOTOはバッチファイル専用です');break;
      case 'IF':     this._if(args);break;
      case 'FOR':    this._for(args);break;
      case 'EXIT':   this.term.println('シェルを終了できません（ここはDOSです）');break;
      case 'HELP':   this._help(args);break;
      default:       this._runFile(name,args);break;
    }
  }

  _dir(args) {
    let tgt=[...this.cwdParts],wide=false,bare=false;
    const filtered=args.filter(a=>{
      if(a.toUpperCase()==='/W'){wide=true;return false;}
      if(a.toUpperCase()==='/B'){bare=true;return false;}
      if(a.toUpperCase()==='/A') return false;
      return true;
    });
    if(filtered.length){
      const[dp]=this._splitPath(filtered[0]);
      tgt=[...this.cwdParts,...dp];
    }
    const entries=this.disk.listDir(tgt);
    if(entries===null){this.term.println('指定されたパスが見つかりません');return;}
    if(!bare){
      this.term.println(` ドライブ A のボリュームラベルは MYDOS`);
      this.term.println(` ディレクトリ: ${this.cwdStr()}`);
      this.term.println('');
    }
    let fc=0,dc=0,tb=0;
    if(wide){
      const ns=entries.map(e=>(e.attr&0x10)?`[${e.name}]`:e.name);
      for(let i=0;i<ns.length;i++){
        this.term.print(ns[i].padEnd(16));
        if((i+1)%5===0)this.term.println('');
      }
      if(ns.length%5)this.term.println('');
    } else {
      if(!bare&&entries.length===0) this.term.println('ファイルがありません');
      for(const e of entries){
        if(e.attr&0x10){dc++;if(!bare)this.term.println(`${e.name.padEnd(20)}<DIR>`);else this.term.println(e.name);}
        else{fc++;tb+=e.size;if(!bare)this.term.println(`${e.name.padEnd(20)}${String(e.size).padStart(10)} バイト`);else this.term.println(e.name);}
      }
    }
    if(!bare){
      this.term.println('');
      this.term.println(`       ${fc} 個のファイル    ${tb.toLocaleString()} バイト`);
      this.term.println(`       ${dc} 個のディレクトリ  ${(this.disk.freeClusters()*512).toLocaleString()} バイトの空き領域`);
    }
  }

  _cd(args) {
    if(!args[0]){this.term.println(this.cwdStr());return;}
    const t=args[0];
    if(t==='\\'||t==='A:\\'){this.cwdParts=[];return;}
    const rel=t.replace(/^A:\\/i,'').replace(/\\/g,'/');
    const newP=[...this.cwdParts];
    for(const p of rel.split('/').filter(Boolean)){
      if(p==='.') continue;
      if(p==='..'){if(newP.length)newP.pop();}
      else newP.push(p.toUpperCase());
    }
    if(!this.disk._resolveDirSectors(newP)){this.term.println('指定されたパスが見つかりません');return;}
    this.cwdParts=newP;
  }

  _md(args) {
    if(!args[0]){this.term.println('ディレクトリ名を指定してください');return;}
    const[dp,fn]=this._splitPath(args[0]);
    try{this.disk.mkdir([...this.cwdParts,...dp],fn);this.disk.flush();}
    catch(e){this.term.println(e.message);}
  }

  _rd(args) {
    if(!args[0]){this.term.println('ディレクトリ名を指定してください');return;}
    const[dp,fn]=this._splitPath(args[0]);
    const fp=[...this.cwdParts,...dp,fn.toUpperCase()];
    const ent=this.disk.listDir(fp);
    if(ent===null){this.term.println('ディレクトリが見つかりません');return;}
    if(ent.filter(e=>e.name!=='.'&&e.name!=='..').length>0){this.term.println('ディレクトリは空ではありません');return;}
    this.disk.deleteEntry([...this.cwdParts,...dp],fn.toUpperCase());
    this.disk.flush();
  }

  _type(args) {
    if(!args[0]){this.term.println('ファイル名を指定してください');return;}
    const[dp,fn]=this._splitPath(args[0]);
    const data=this.disk.readFile([...this.cwdParts,...dp],fn);
    if(!data){this.term.println(`ファイルが見つかりません - ${fn}`);return;}
    let line='';
    for(let i=0;i<data.length;i++){
      const c=data[i];if(c===0x1A)break;if(c===0x0D)continue;
      if(c===0x0A){this.term.println(line);line='';}
      else line+=(c>=0x20&&c<0x7F)?String.fromCharCode(c):'.';
    }
    if(line)this.term.println(line);
  }

  _copy(args) {
    if(!args[0]){this.term.println('コピー元を指定してください');return;}
    const[sdp,sfn]=this._splitPath(args[0]);
    const data=this.disk.readFile([...this.cwdParts,...sdp],sfn);
    if(!data){this.term.println(`ファイルが見つかりません - ${sfn}`);return;}
    let dfn=sfn,dbase=[...this.cwdParts];
    if(args[1]){const[ddp,dfname]=this._splitPath(args[1]);dbase=[...this.cwdParts,...ddp];dfn=dfname||sfn;}
    try{this.disk.writeFile(dbase,dfn,data);this.disk.flush();this.term.println('        1 個のファイルをコピーしました');}
    catch(e){this.term.println(e.message);}
  }

  _xcopy(args) { this._copy(args.filter(a=>!a.startsWith('/'))); }

  _del(args) {
    if(!args[0]){this.term.println('ファイル名を指定してください');return;}
    const t=args[0];
    if(t==='*.*'||t==='*'){
      const ent=this.disk.listDir(this.cwdParts)||[];
      let cnt=0;
      for(const e of ent)if(!(e.attr&0x10)){this.disk.deleteEntry(this.cwdParts,e.name);cnt++;}
      this.disk.flush();this.term.println(`${cnt} 個のファイルを削除しました`);return;
    }
    const[dp,fn]=this._splitPath(t);
    if(this.disk.deleteEntry([...this.cwdParts,...dp],fn)){this.disk.flush();}
    else this.term.println(`ファイルが見つかりません - ${fn}`);
  }

  _ren(args) {
    if(args.length<2){this.term.println('ファイル名を2つ指定してください');return;}
    const[dp,on]=this._splitPath(args[0]);
    if(this.disk.renameEntry([...this.cwdParts,...dp],on,args[1].toUpperCase()))this.disk.flush();
    else this.term.println(`ファイルが見つかりません - ${on}`);
  }

  _move(args) {
    if(args.length<2){this.term.println('移動元と移動先を指定してください');return;}
    const[sdp,sfn]=this._splitPath(args[0]);
    const[ddp,dfn]=this._splitPath(args[1]);
    const data=this.disk.readFile([...this.cwdParts,...sdp],sfn);
    if(!data){this.term.println(`ファイルが見つかりません - ${sfn}`);return;}
    try{
      this.disk.writeFile([...this.cwdParts,...ddp],dfn||sfn,data);
      this.disk.deleteEntry([...this.cwdParts,...sdp],sfn);
      this.disk.flush();this.term.println(`${sfn} を移動しました`);
    }catch(e){this.term.println(e.message);}
  }

  _echo(args) {
    if(!args.length||args[0].toUpperCase()==='ON'||args[0].toUpperCase()==='OFF'){this.term.println('ECHO is ON');return;}
    this.term.println(args.join(' '));
  }

  _set(args) {
    if(!args.length){for(const[k,v]of Object.entries(this.env))this.term.println(`${k}=${v}`);return;}
    const full=args.join(' '),eq=full.indexOf('=');
    if(eq>=0){const k=full.slice(0,eq).toUpperCase(),v=full.slice(eq+1);if(v)this.env[k]=v;else delete this.env[k];}
    else{const k=full.toUpperCase();this.term.println(this.env[k]!==undefined?`${k}=${this.env[k]}`:`環境変数 ${k} は定義されていません`);}
  }

  _path(args) {
    if(!args[0]){this.term.println('PATH='+this.env.PATH);return;}
    this.env.PATH=args.join(' ');
  }

  _promptCmd(args) {
    if(!args[0]){this.term.println('PROMPT='+this.env.PROMPT);return;}
    this.env.PROMPT=args.join(' ');
  }

  _format(args) {
    if(!args.some(a=>a.toUpperCase()==='/Y')){
      this.term.println('警告: すべてのデータが失われます！');
      this.term.println('フォーマットするには FORMAT /Y を使用してください');
      return;
    }
    this.disk.format();this.cwdParts=[];
    this.term.println('フォーマット完了\n1,457,664 バイト  使用可能');
  }

  _chkdsk() {
    const free=this.disk.freeClusters();
    const max=Math.floor(this.disk.SECTORS_PER_FAT*512*2/3)-2;
    this.term.println(` 1,457,664 バイト  総ディスク領域`);
    this.term.println(`   ${((max-free)*512).toLocaleString()} バイト  使用済み`);
    this.term.println(`   ${(free*512).toLocaleString()} バイト  使用可能`);
    this.term.println('\n   655,360 バイト  総メモリ\n   655,360 バイト  使用可能');
  }

  _attrib(args) {
    const entries=this.disk.listDir(this.cwdParts)||[];
    for(const e of entries){
      const a=e.attr;
      this.term.println([(a&0x20?'A':' '),(a&0x02?'H':' '),(a&0x01?'R':' '),(a&0x04?'S':' ')].join('')+`  A:\\${[...this.cwdParts,e.name].join('\\')}`);
    }
  }

  _find(args) {
    const q=args.find(a=>a.startsWith('"')&&a.endsWith('"'));
    if(!q){this.term.println('使用法: FIND "文字列" [ファイル名]');return;}
    const needle=q.slice(1,-1).toLowerCase();
    const fileArg=args.find(a=>!a.startsWith('"')&&!a.startsWith('/'));
    const entries=fileArg?[{name:fileArg}]:(this.disk.listDir(this.cwdParts)||[]).filter(e=>!(e.attr&0x10));
    for(const e of entries){
      const[dp,fn]=this._splitPath(e.name);
      const data=this.disk.readFile([...this.cwdParts,...dp],fn);
      if(!data)continue;
      const text=new TextDecoder().decode(data);
      let found=false;
      text.split('\n').forEach(l=>{
        if(l.toLowerCase().includes(needle)){
          if(!found){this.term.println(`---------- ${fn}`);found=true;}
          this.term.println(l);
        }
      });
    }
  }

  _sort(args) {
    if(!args[0]){this.term.println('使用法: SORT ファイル名');return;}
    const[dp,fn]=this._splitPath(args[0]);
    const data=this.disk.readFile([...this.cwdParts,...dp],fn);
    if(!data){this.term.println('ファイルが見つかりません');return;}
    new TextDecoder().decode(data).split('\n').sort().forEach(l=>this.term.println(l));
  }

  _tree(args) {
    this.term.println('A:\\'+this.cwdParts.join('\\'));
    this._treeRec(this.cwdParts,'');
  }

  _treeRec(parts,pfx) {
    const dirs=(this.disk.listDir(parts)||[]).filter(e=>(e.attr&0x10)&&e.name!=='.'&&e.name!=='..');
    dirs.forEach((d,i)=>{
      const last=i===dirs.length-1;
      this.term.println(`${pfx}${last?'└':'├'}── ${d.name}`);
      this._treeRec([...parts,d.name],pfx+(last?'    ':'│   '));
    });
  }

  _mem() {
    this.term.println('メモリタイプ             合計      使用済み      空き');
    this.term.println('------------------- -------- ------------ --------');
    this.term.println('通常メモリ            655,360            0   655,360');
    this.term.println('');
    this.term.println('合計メモリ            655,360            0   655,360');
  }

  _if(args) {
    // 簡易: IF EXIST file command
    const raw=args.join(' ');
    const m=raw.match(/^EXIST\s+(\S+)\s+(.+)$/i);
    if(m){
      const[dp,fn]=this._splitPath(m[1]);
      const exists=!!this.disk.readFile([...this.cwdParts,...dp],fn);
      if(exists){const p=this._splitArgs(m[2]);this._dispatch(p[0].toUpperCase(),p.slice(1));}
      return;
    }
    const mn=raw.match(/^NOT\s+EXIST\s+(\S+)\s+(.+)$/i);
    if(mn){
      const[dp,fn]=this._splitPath(mn[1]);
      const exists=!!this.disk.readFile([...this.cwdParts,...dp],fn);
      if(!exists){const p=this._splitArgs(mn[2]);this._dispatch(p[0].toUpperCase(),p.slice(1));}
      return;
    }
    const eq=raw.match(/^(\S+)==(\S+)\s+(.+)$/);
    if(eq&&eq[1]===eq[2]){const p=this._splitArgs(eq[3]);this._dispatch(p[0].toUpperCase(),p.slice(1));}
  }

  _for(args) { this.term.println('[FOR] 簡易サポートのみ'); }

  _help(args) {
    const cmds=[
      'ATTRIB BREAK CALL CD/CHDIR CHKDSK CLS COPY DATE DEL/ERASE',
      'DIR DISKCOMP ECHO EDIT EXIT FIND FOR FORMAT GOTO HELP IF',
      'LABEL MD/MKDIR MEM MORE MOVE PATH PAUSE PRINT PROMPT RD/RMDIR',
      'REM REN/RENAME SET SORT TIME TREE TYPE VER VERIFY VOL XCOPY',
    ];
    if(args[0]){
      this.term.println(`${args[0].toUpperCase()} の詳細ヘルプは未実装です`);return;
    }
    this.term.println('コマンドの一覧:');
    this.term.println('');
    cmds.forEach(l=>this.term.println('  '+l));
    this.term.println('');
    this.term.println('特定のコマンドの詳細は HELP コマンド名 と入力してください');
  }

  _runFile(name,args) {
    for(const fn of [name+'.COM',name+'.EXE',name+'.BAT',name]){
      const data=this.disk.readFile(this.cwdParts,fn);
      if(data){
        if(fn.endsWith('.BAT')){
          const lines=new TextDecoder().decode(data).split('\n').map(l=>l.trim()).filter(l=>l&&!l.toUpperCase().startsWith('REM'));
          for(const l of lines){const p=this._splitArgs(l);if(p[0])this._dispatch(p[0].toUpperCase(),p.slice(1));}
          return;
        }
        if(typeof CPU8086!=='undefined'&&typeof Memory!=='undefined'){
          this._execCOM(fn,data);
        } else {
          this.term.println(`[${fn} - ${data.length}B - cpu8086.jsが必要です]`);
        }
        return;
      }
    }
    this.term.println(`'${name}' は内部コマンドでも外部コマンドでもありません`);
  }

  _execCOM(fn,data) {
    // 既存のCPU実行があれば停止
    if(window._cpuRunning){
      this.term.println('既に実行中です');return;
    }
    this.term.println('実行: '+fn+' ('+data.length+'B)');
    try {
      const mem=new Memory();
      const cpu=new CPU8086(mem);
      cpu.installBIOS();
      const ORG=0x0100;
      mem.load(ORG,data);
      cpu.reg.cs=0;cpu.reg.ds=0;cpu.reg.es=0;cpu.reg.ss=0;
      cpu.reg.sp=0xFFFE;cpu.reg.ip=ORG;
      const term=this.term;
      const shell=this;

      // VRAMを直接画面に表示するモードに切り替え
      window._cpuInstance=cpu;
      window._cpuMem=mem;
      window._cpuRunning=true;

      // onBiosOutputは使わず、VRAMを毎フレームレンダリング
      cpu.onBiosOutput=()=>{};

      const CYCLES_PER_TICK=100000;
      const tick=()=>{
        if(!window._cpuRunning) return;
        const t0=performance.now();
        let ran=0;
        while(ran<CYCLES_PER_TICK){
          if(cpu.halted) break; // キー待ちor HLT → 次のtickへ
          cpu.step();
          ran++;
          if(performance.now()-t0>14) break; // 14ms超えたら中断して次フレーム
        }

        // VRAMレンダリング
        if(window.renderVRAM) window.renderVRAM();

        // 本物のHLTかどうか判定
        // INT 16hキー待ち: haltedだがipはINT命令(0xCD)を指す
        // 本物のHLT: haltedで次命令がF4かF4の次
        if(cpu.halted){
          const physIP=(cpu.reg.cs*16+cpu.reg.ip)&0xFFFFF;
          const op=mem.read8(physIP);
          if(op===0xF4){
            // 本物のHLT → 終了
            window._cpuRunning=false;
            window._cpuInstance=null;
            window._cpuMem=null;
            window.exitVRAMMode();
            term.println('');
            shell.prompt();
            if(window.onDiskChange)window.onDiskChange();
            return;
          }
          // キー待ち(INT 16h) → halted解除せずに次tickへ（キー入力で解除）
        }
        requestAnimationFrame(tick);
      };
      tick();
    }catch(e){
      this.term.println('実行エラー: '+e.message);
      window._cpuRunning=false;
    }
  }


  _splitPath(p) {
    p=(p||'').replace(/^A:\\/i,'').replace(/\\/g,'/');
    const parts=p.split('/').filter(Boolean);
    if(!parts.length)return[[],'']; 
    const fn=parts.pop().toUpperCase();
    return[parts.map(s=>s.toUpperCase()),fn];
  }

  _splitArgs(line) {
    const a=[];let cur='',inQ=false;
    for(const c of line){
      if(c==='"'){inQ=!inQ;continue;}
      if(c===' '&&!inQ){if(cur){a.push(cur);cur='';}}else cur+=c;
    }
    if(cur)a.push(cur);return a;
  }
}

// ============================================================
// ターミナル
// ============================================================
class Terminal {
  constructor(el){this.el=el;this.buf='';this.MAX=80000;}
  print(s){this.buf+=s;this._flush();}
  println(s=''){this.buf+=(s||'')+'\n';this._flush();}
  clear(){this.buf='';this.el.textContent='';}
  _flush(){
    if(this.buf.length>this.MAX)this.buf=this.buf.slice(-this.MAX);
    this.el.textContent=this.buf;
    this.el.scrollTop=this.el.scrollHeight;
  }
}

// ============================================================
// 公開API
// ============================================================
window.MSDos={
  disk:null,shell:null,term:null,

  init(outputEl,inputEl){
    this.term=new Terminal(outputEl);
    this.disk=new FAT12Disk();
    if(!this.disk.isFormatted()){
      this.disk.format();
      this.term.println('[新しいディスクをフォーマットしました]');
    } else {
      this.term.println('[ディスクをlocalStorageから読み込みました]');
    }
    this.shell=new DOSShell(this.disk,this.term);
    this.shell.start();

    inputEl.addEventListener('keydown',e=>{
      if(e.key==='Enter'){
        const line=inputEl.value;
        this.term.print(line);
        inputEl.value='';
        this.shell.execute(line);
        if(window.onDiskChange)window.onDiskChange();
      } else if(e.key==='ArrowUp'){
        e.preventDefault();
        const h=this.shell.history;
        if(!h.length)return;
        this.shell.histIdx=Math.min(this.shell.histIdx+1,h.length-1);
        inputEl.value=h[this.shell.histIdx];
      } else if(e.key==='ArrowDown'){
        e.preventDefault();
        this.shell.histIdx=Math.max(this.shell.histIdx-1,-1);
        inputEl.value=this.shell.histIdx<0?'':this.shell.history[this.shell.histIdx];
      } else if(e.key==='Tab'){
        e.preventDefault();
        this._tabComplete(inputEl);
      }
    });
  },

  _tabComplete(inputEl){
    const val=inputEl.value;
    const parts=val.split(/\s+/);
    const last=parts[parts.length-1];
    if(!last)return;
    const entries=this.disk.listDir(this.shell.cwdParts)||[];
    const matches=entries.filter(e=>e.name.toUpperCase().startsWith(last.toUpperCase()));
    if(matches.length===1){parts[parts.length-1]=matches[0].name;inputEl.value=parts.join(' ');}
    else if(matches.length>1){
      this.term.println('');
      matches.forEach(m=>this.term.print(m.name.padEnd(14)));
      this.term.println('');
      this.shell.prompt();
    }
  },

  saveCom(name,bytes){
    try{this.disk.writeFile([],name,new Uint8Array(bytes));this.disk.flush();if(window.onDiskChange)window.onDiskChange();return true;}
    catch(e){return e.message;}
  },

  importFile(name,bytes){return this.saveCom(name.toUpperCase(),bytes);},
  downloadImg(){this.disk.download('disk.img');},

  format(){
    this.disk.format();this.shell.cwdParts=[];
    this.term.println('[ディスクをフォーマットしました]');
    if(window.onDiskChange)window.onDiskChange();
  },

  getFiles(){return this.disk?this.disk.listDir([])||[]:[]; }
};