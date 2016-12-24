format PE console
entry main

include 'macro/import64.inc'

section '.data' data readable writeable
msg db "hello world!",0
p db "pause>nul",0
val dd 4241h

section '.code' code readable executable
main:
mov dword [esp],val
call [printf]
call [exit]

section '.idata' import data readable
library msvcrt,'msvcrt.dll'
import msvcrt,\
printf,'printf',\
system,'system',\
exit,'exit'









;include "win64ax.inc" 
;
;.data 
;Caption db 'Win64 assembly program',0 
;Message db 'Sup Nerds!',0 
;
;.code 
;start: 
;xor r9d,r9d 
;lea r8,[Caption] 
;lea rdx,[Message] 
;xor rcx,rcx 
;call [MessageBox] 
;mov ecx,eax 
;invoke ExitProcess,0 
;.end start 
;
