ORG 0100h

start:
    MOV AX, 3
    INT 10h

mainloop:
    MOV SI, prompt
    CALL print_str

    LEA DI, [0400h]
    CALL line_input_with_cursor

    MOV SI, msg_cipher
    CALL print_str

    LEA SI, [0400h]
    LEA DI, [0500h]

rot13_loop:
    LODSB
    OR  AL, AL
    JZ  rot13_end
    CALL to_upper
    CMP AL, 41h
    JB rot13_etc
    CMP AL, 5Ah
    JA rot13_etc
    SUB AL, 41h
    ADD AL, 13
    CMP AL, 26
    JB rot13_do
    SUB AL, 26
rot13_do:
    ADD AL, 41h
rot13_etc:
    MOV [DI], AL
    INC DI
    JMP rot13_loop

rot13_end:
    MOV BYTE [DI], 0
    LEA SI, [0500h]
    CALL print_str
    CALL print_nl
    JMP mainloop

;----- 入力 with カーソルアンダーバー -----
; DI=バッファ, ENTERでNULL終端
line_input_with_cursor:
    XOR CX, CX
.cursor_show:
    ; カーソル"_"を表示
    MOV AH, 0Eh
    MOV AL, 5Fh    ; '_'
    INT 10h
    MOV AL, 08h    ; BSで戻る
    INT 10h

.get_key:
    MOV AH, 00h
    INT 16h

    ; カーソル消す
    PUSH AX
    MOV AH, 0Eh
    MOV AL, 20h
    INT 10h
    MOV AL, 08h
    INT 10h
    POP AX

    CMP AL, 0Dh
    JE .done
    CMP AL, 08h
    JE .bs
    CMP CX, 63
    JAE .cursor_show
    MOV [DI], AL
    INC DI
    INC CX
    MOV AH, 0Eh
    INT 10h
    JMP .cursor_show

.bs:
    CMP CX, 0
    JE .cursor_show
    DEC DI
    DEC CX
    MOV AH, 0Eh
    MOV AL, 08h
    INT 10h
    MOV AL, 20h
    INT 10h
    MOV AL, 08h
    INT 10h
    JMP .cursor_show

.done:
    MOV BYTE [DI], 0
    RET

print_str:
    MOV AH, 0Eh
.ps_loop:
    LODSB
    OR AL, AL
    JZ .end
    INT 10h
    JMP .ps_loop
.end:  RET

print_nl:
    MOV AH, 0Eh
    MOV AL, 0Dh
    INT 10h
    MOV AL, 0Ah
    INT 10h
    RET

to_upper:
    CMP AL, 61h
    JB .caps
    CMP AL, 7Ah
    JA .caps
    SUB AL, 20h
.caps:  RET

prompt:     DB 'PLAINTEXT: ',0
msg_cipher: DB 0Dh,0Ah,'CIPHER: ',0