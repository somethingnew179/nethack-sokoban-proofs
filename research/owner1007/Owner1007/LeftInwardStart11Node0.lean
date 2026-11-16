import Owner1007.LeftInwardStart11Data
namespace Owner1007.LeftInwardStart11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid (0:Fin 2)=true := by decide +kernel
#print axioms node0
end Owner1007.LeftInwardStart11
