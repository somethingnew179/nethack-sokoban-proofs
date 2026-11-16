import Owner1007.LeftFourLane11Data
namespace Owner1007.LeftFourLane11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem node00 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel
#print axioms node00
theorem node01 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true := by decide +kernel
#print axioms node01
theorem node02 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 2=true := by decide +kernel
#print axioms node02
theorem node03 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 3=true := by decide +kernel
#print axioms node03
theorem node04 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 4=true := by decide +kernel
#print axioms node04
theorem node05 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 5=true := by decide +kernel
#print axioms node05
theorem node06 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 6=true := by decide +kernel
#print axioms node06
theorem node07 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 7=true := by decide +kernel
#print axioms node07
theorem node08 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 8=true := by decide +kernel
#print axioms node08
theorem node09 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 9=true := by decide +kernel
#print axioms node09
theorem node10 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 10=true := by decide +kernel
#print axioms node10
theorem node11 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 11=true := by decide +kernel
#print axioms node11
theorem node12 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 12=true := by decide +kernel
#print axioms node12
theorem node13 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 13=true := by decide +kernel
#print axioms node13
theorem node14 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 14=true := by decide +kernel
#print axioms node14
theorem node15 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 15=true := by decide +kernel
#print axioms node15
theorem node16 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 16=true := by decide +kernel
#print axioms node16
theorem node17 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 17=true := by decide +kernel
#print axioms node17
theorem node18 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 18=true := by decide +kernel
#print axioms node18
theorem node19 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 19=true := by decide +kernel
#print axioms node19
theorem node20 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 20=true := by decide +kernel
#print axioms node20
theorem floor (i : Fin 21) : region i⊆soko1_1.board.floor := by
 have row : (List.finRange 21).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp row i (by simp)) c member)
theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem nonempty : ∀i,locks i≠[] := by decide +kernel
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1∨i=2∨i=3∨i=4∨i=5∨i=6∨i=7∨i=8∨i=9∨i=10∨i=11∨i=12∨i=13∨i=14∨i=15∨i=16∨i=17∨i=18∨i=19∨i=20 := by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 ·exact node00
 ·exact node01
 ·exact node02
 ·exact node03
 ·exact node04
 ·exact node05
 ·exact node06
 ·exact node07
 ·exact node08
 ·exact node09
 ·exact node10
 ·exact node11
 ·exact node12
 ·exact node13
 ·exact node14
 ·exact node15
 ·exact node16
 ·exact node17
 ·exact node18
 ·exact node19
 ·exact node20
#print axioms closed
end Owner1007.LeftFourLane11
