import Owner1007.LeftInwardPipe11Data
namespace Owner1007.LeftInwardPipe11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node5 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid (5:Fin 6)=true := by decide +kernel
#print axioms node5
end Owner1007.LeftInwardPipe11
