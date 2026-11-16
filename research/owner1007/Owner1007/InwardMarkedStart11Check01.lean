import Owner1007.InwardMarkedStart11Data
namespace Owner1007.InwardMarkedStart11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true:=by decide +kernel
#print axioms node1
end Owner1007.InwardMarkedStart11
