import Owner1007.Front26511Data
namespace Owner1007.Front26511
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨0,by decide⟩=true := by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨1,by decide⟩=true := by decide +kernel
theorem node2 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨2,by decide⟩=true := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks soko1_1.board soko1_1.initial.holes locks region paid ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1∨i=2 := by omega
 rcases choices with rfl|rfl|rfl
 ·exact node0
 ·exact node1
 ·exact node2
#print axioms growing_checked
#print axioms growth
#print axioms closed
end Owner1007.Front26511
