ORG 0100h

; ===========================
; Hello World — BIOS INT 10h
; ===========================

start:
        MOV SI, msg

.loop:
        LODSB
        TEST AL, AL
        JZ  .done
        MOV AH, 0Eh
        MOV BH, 0
        INT 10h
        JMP .loop

.done:
        MOV AX, 4C00h
        INT 21h

msg:    DB 'Hello, 8086!', 0Dh, 0Ah, 0