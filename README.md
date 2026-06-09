# Chess88

Chess88 by Don Berg from 1984 is a replica of Sargon (1978) by Dan and Kathe Spracklen, reimplemented in x86 assembly. The graphics are from Sargon 2 (1980).

However, there are also some minor differences: as White, the computer chooses only the first move `e4`, `d4`, `Nc3` or `Nf3` with equal probability, and the first three moves by the computer are played at Level 1 no matter what level the user chooses, resulting in effectively instant play. This has the unfortunate effect that e.g. as White for any level, a human can play `1. e4 Nf6 2. e5 Ne4? 3. d4 Nc6? 4. f3` winning the Black knight (evaluation about 3 pawns ahead for White, which is winning).

Additionally there are three bugs.

## Bug 1 — Development penalty fires on every move

Sargon gives a small penalty (−2 points) to a Rook or Queen that has already moved, but only in the opening — before move 7. The idea is to discourage bringing the queen or rooks out too early, when they can be chased around and lose tempo. Once the opening is over, the penalty is supposed to switch off entirely.

Chess88 mistranslated the single "skip the penalty" jump. As a result, a developed Rook or Queen is penalised on every move of the game, not just early on.

## Bug 2 — A pinned attacker that legally attacks is wrongly ignored

**In plain English**

A piece is pinned when it cannot legally move because doing so would expose its own king (or queen) to capture along the line the pin runs on. But a pinned piece is not helpless: it can still attack along the pin line itself. A bishop pinned on a diagonal still attacks every square on that diagonal; a rook pinned on a file still attacks up and down that file. Moving along the pin keeps the king shielded, so those attacks are perfectly legal.

When Sargon counts how many pieces attack and defend a square (to decide whether a capture is safe), it deliberately skips pieces that are pinned — unless a pinned piece is attacking straight along its own pin line, in which case it still counts. Chess88's port of that "is this piece pinned, and if so does it still attack?" check has two separate defects, and both of them cause a legal attacker to be wrongly dropped from the count.

The consequence is in the exchange evaluator. With an attacker missing, Chess88's static exchange calculator (`XCHNG`) sees fewer pieces bearing on a square than really do. It can then decide a defended piece is safe to capture, or that a capture wins material, when the omitted pinned-but-legal attacker would have changed the verdict. In `chess88.c` this is the `eval_c88_pin` flag.

## Bug 3 — Attack list cleared with leftover garbage in every high byte

Before counting who attacks a square, Sargon zeroes a small scratch "attack list." On the Z80 that clear is clean: every slot ends up truly zero. The 8086 port cleared the list a word (two bytes) at a time but only zeroed half of the value register — it set `al` to 0 and forgot `ah`. The leftover garbage sitting in `ah` therefore got written into the high byte of every empty list slot, so each empty slot became `0x(AH)00` instead of `0x0000`.

That matters because the routine that later walks the list treats "all zero" as "empty slot, skip it." A slot that reads `0x(AH)00` is non-zero in its high byte, so the walker does not skip it — it stops on a phantom attacker whose actual value (the low byte) is 0. The exchange calculator (`XCHNG`) then sees a first attacker worth 0, gives up early, and scores the square as if it were undefended/safe — under-counting the material by up to half a pawn.

I had Claude Code analyse chess88 in conjunction with the original Z80 source code, producing the following.

`chess88.c` is a reimplementation of chess88.exe in C99. Additionally, it can be compiled with `-DSTOCK_SARGON` to correct these bugs.

`chess88-fixed.exe` is the original `chess88.exe` of Don Berg with the opcodes edited to correct these bugs; effectively turning it into a nearly identical clone of Sargon.

| File offset | Old → New | Instruction | Bug fixed |
| --- | --- | --- | --- |
| `0x0EF0–0x0EF1` | `73 11` → `EB 2A` | `jnc 0xd03` → `jmp 0xd1c` | 1 — dev penalty no longer fires from move 7 on |
| `0x0291` | `65` → `66` | `lea di,[0x165]` → `[0x166]` | 2a — pin scan now reads the 1-indexed list |
| `0x02A5` | `EE` → `08` | `jz 0x94` → `jz 0xae` | 2b — along-pin attacker counted, no misfire loop |
| `0x02AB` | `E8` → `02` | `jz 0x94` → `jz 0xae` | 2c — same, second branch |
| `0x0F1C–0x0F1D` | `B0 00` → `31 C0` | `mov al,0` → `xor ax,ax` | 3 — attack-list clears to clean `0x0000` |
