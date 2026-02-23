ORG 0100h

start:
        ; 1. 画面リセット
        MOV AX, 0003h
        INT 10h

        ; 2. 1行目に説明書きを表示 (INT 10h, AH=13h は複雑なので 0Eh で地道に書く)
        ; カーソルを行0, 列0へ
        MOV AH, 02h
        MOV BH, 0
        MOV DX, 0000h ; DH=0(行), DL=0(列)
        INT 10h

        ; "ESC is exit" を表示 (ASCII直書き)
        MOV AH, 0Eh
        MOV AL, 45h ; 'E'
        INT 10h
        MOV AL, 53h ; 'S'
        INT 10h
        MOV AL, 43h ; 'C'
        INT 10h
        MOV AL, 20h ; Space
        INT 10h
        MOV AL, 69h ; 'i'
        INT 10h
        MOV AL, 73h ; 's'
        INT 10h
        MOV AL, 20h ; Space
        INT 10h
        MOV AL, 65h ; 'e'
        INT 10h
        MOV AL, 78h ; 'x'
        INT 10h
        MOV AL, 69h ; 'i'
        INT 10h
        MOV AL, 74h ; 't'
        INT 10h

        ; 3. ノート(0200h)リセット
        MOV BX, 0200h
        MOV CX, 25
clear_notes:
        MOV BYTE [BX], 0
        INC BX
        LOOP clear_notes

        ; 4. エディタ開始位置（行1）へ移動
        MOV AH, 02h
        MOV BH, 0
        MOV DX, 0100h ; DH=1(行), DL=0(列)
        INT 10h

echo_loop:
        ; --- カーソル表示 ---
        MOV AH, 0Eh
        MOV AL, 5Fh ; '_'
        INT 10h
        MOV AL, 08h ; Backspace
        INT 10h

        ; --- キー入力 ---
        MOV AH, 00h
        INT 16h

        ; --- '_' を消す ---
        PUSH AX
        MOV AH, 0Eh
        MOV AL, 20h
        INT 10h
        MOV AL, 08h
        INT 10h
        POP AX

        ; --- 特殊キー判定 ---
        CMP AL, 1Bh ; ESC
        JE  exit_prog
        CMP AL, 08h ; Backspace
        JE  smart_backspace
        CMP AL, 0Dh ; Enter
        JE  handle_enter

        ; --- 普通の文字表示 ---
        MOV AH, 0Eh
        MOV BL, 07h
        INT 10h

        ; 位置保存
        MOV AH, 03h
        MOV BH, 0
        INT 10h
        MOV BX, 0200h
        MOV AL, DH
        MOV AH, 0
        ADD BX, AX
        MOV [BX], DL
        JMP echo_loop

smart_backspace:
        MOV AH, 03h
        MOV BH, 0
        INT 10h
        CMP DL, 0
        JNE .on_the_line
        CMP DH, 1      ; 行1より上には行かせないガード
        JE  echo_loop
        DEC DH
        MOV BX, 0200h
        MOV AL, DH
        MOV AH, 0
        ADD BX, AX
        MOV DL, [BX]
        JMP .apply_move
.on_the_line:
        DEC DL
.apply_move:
        MOV AH, 02h
        MOV BH, 0
        INT 10h
        MOV AH, 0Ah
        MOV AL, 20h
        MOV CX, 1
        INT 10h
        JMP echo_loop

handle_enter:
        MOV AH, 0Eh
        MOV AL, 0Dh
        INT 10h
        MOV AL, 0Ah
        INT 10h
        ; 改行後の位置をノートに0で記録
        MOV AH, 03h
        MOV BH, 0
        INT 10h
        MOV BX, 0200h
        MOV AL, DH
        MOV AH, 0
        ADD BX, AX
        MOV BYTE [BX], 0
        JMP echo_loop

exit_prog:
        ; 画面一番左上に '!' (21h) を表示して停止
        MOV AH, 02h
        MOV BH, 0
        MOV DX, 0000h ; 行0, 列0
        INT 10h
        MOV AH, 0Eh
        MOV AL, 21h   ; '!'
        INT 10h
stop:
        HLT
        JMP stop