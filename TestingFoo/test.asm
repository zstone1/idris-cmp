include "win64ax.inc" 

.data 
Caption db 'Win64 assembly program',0 
Message db 'Sup Nerds!',0 

.code 
start: 
xor r9d,r9d 
lea r8,[Caption] 
lea rdx,[Message] 
xor rcx,rcx 
call [MessageBox] 
mov ecx,eax 
invoke ExitProcess,0 
.end start 

