ORG 0100h

start:
    ; 1. 画面リセット (80x25 Text Mode)
    mov ax, 0003h
    int 10h

    ; 2. バッファクリア (0300h-0600h)
    mov bx, 0300h
    mov cx, 0300h       ; 768バイト分
clear_lp:
    mov byte [bx], 0
    inc bx
    loop clear_lp

    ; 3. 入力1 (格納先: 0300h)
    mov di, 0300h
    call input_long_number

    ; '+' (2Bh) 表示
    mov al, 2Bh
    call print_char
    call print_newline

    ; 4. 入力2 (格納先: 0400h)
    mov di, 0400h
    call input_long_number

    ; '=' (3Dh) 表示
    mov al, 3Dh
    call print_char
    call print_newline

    ; 5. 筆算 (0300h + 0400h -> 0500h)
    call calculate_addition

    ; 6. 結果表示
    call display_result

    ; --- 追加: 終了前のキー待ち処理 ---
    call print_newline
    ; メッセージ「Press Any Key to Exit...」
    mov bx, exit_msg
    call print_string

    ; [重要] 古いEnterの残像を掃除
.flush:
    mov ah, 01h
    int 16h
    jz .wait_real
    mov ah, 00h
    int 16h
    jmp .flush

.wait_real:
    mov ah, 00h         ; 本物の「新しいキー」を待つ
    int 16h

    ; 終了
    mov ax, 0003h       ; 画面を戻す
    int 10h
    mov ah, 4Ch

    ; CPUを完全に止める（念のため）
    hlt
    hlt
    hlt

; --- 文字列表示補助 ---
print_string:
    mov al, [bx]
    cmp al, 0
    je .done
    call print_char
    inc bx
    jmp print_string
.done:
    ret

exit_msg: db "Press Any Key to Exit...", 0

; --- 入力ルーチン ---
input_long_number:
    xor cx, cx          ; 桁数
.loop:
    mov ah, 00h         ; キー待ち
    int 16h

    cmp al, 0Dh         ; Enter
    je .done
    cmp al, 08h         ; Backspace
    je .backspace
    cmp al, 1Bh         ; ESCで即終了
    je exit_now
    cmp al, 30h         ; '0'
    jb .loop
    cmp al, 39h         ; '9'
    ja .loop

    ; 数字入力
    push ax
    mov ah, 0Eh
    int 10h             ; エコーバック
    pop ax
    sub al, 30h         ; ASCII -> 数値
    mov [di], al
    inc di
    inc cx
    jmp .loop

.backspace:
    jcxz .loop
    dec di
    dec cx
    mov al, 08h         ; 戻る
    call print_char
    mov al, 20h         ; 空白で消す
    call print_char
    mov al, 08h         ; また戻る
    call print_char
    jmp .loop

.done:
    mov byte [di], 0FFh ; 終端
    call print_newline
    ret

exit_now:
    mov ah, 4Ch
    int 21h

; --- 筆算コア ---
calculate_addition:
    mov si, 0300h
.f1: cmp byte [si], 0FFh
    je .found1
    inc si
    jmp .f1
.found1: dec si

    mov bx, 0400h
.f2: cmp byte [bx], 0FFh
    je .found2
    inc bx
    jmp .f2
.found2: dec bx

    mov di, 0500h       ; 結果(逆順)
    xor dh, dh          ; Carry

.add_loop:
    xor ax, ax
    cmp si, 0300h
    jl .skip1
    mov al, [si]
    dec si
.skip1:
    cmp bx, 0400h
    jl .skip2
    add al, [bx]
    dec bx
.skip2:
    add al, dh          ; 繰り上がり足す
    mov dh, 0
    cmp al, 0Ah         ; 10以上か
    jl .no_c
    sub al, 0Ah
    mov dh, 1
.no_c:
    mov [di], al
    inc di
    cmp si, 0300h
    jge .add_loop
    cmp bx, 0400h
    jge .add_loop
    
    test dh, dh
    jz .final
    mov [di], dh
    inc di
.final:
    mov byte [di], 0FFh
    ret

; --- 表示ルーチン ---
display_result:
    mov si, 0500h
    xor cx, cx
.push_lp:
    cmp byte [si], 0FFh
    je .pop_lp
    mov al, [si]
    push ax
    inc si
    inc cx
    jmp .push_lp
.pop_lp:
    jcxz .done_disp
    pop ax
    add al, 30h         ; 数値 -> ASCII '0'
    call print_char
    loop .pop_lp
.done_disp:
    call print_newline
    ret

; --- 補助 ---
print_char:
    mov ah, 0Eh
    int 10h
    ret

print_newline:
    mov al, 0Dh
    call print_char
    mov al, 0Ah
    call print_char
    ret