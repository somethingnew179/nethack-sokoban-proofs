import Owner1007.PreCage12North0
import Owner1007.PreCage12North1
import Owner1007.PreCage12North2
import Owner1007.PreCage12North3
import Owner1007.PreCage12North4
import Owner1007.PreCage12North5
import Owner1007.PreCage12North6
import Owner1007.PreCage12North7
import Owner1007.PreCage12North8
import Owner1007.PreCage12North9
import Owner1007.PreCage12Ring0
import Owner1007.PreCage12Ring1
import Owner1007.PreCage12Ring2
import Owner1007.PreCage12Ring3
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem reverse_checked : Geometry.reverseCheck soko1_2.board=true := by decide +kernel
theorem north_checked (i : Fin 10) : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid i=true := by
 obtain ⟨i,h⟩ := i
 have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact north0
 · exact north1
 · exact north2
 · exact north3
 · exact north4
 · exact north5
 · exact north6
 · exact north7
 · exact north8
 · exact north9
theorem north_tagged (i : Fin 10) : tagPart northLocks northRegion northPaid northAllowed i=true := by
 obtain ⟨i,h⟩ := i
 have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact north0_tags
 · exact north1_tags
 · exact north2_tags
 · exact north3_tags
 · exact north4_tags
 · exact north5_tags
 · exact north6_tags
 · exact north7_tags
 · exact north8_tags
 · exact north9_tags
theorem north_floor (i : Fin 10) : northRegion i⊆soko1_2.board.floor := by
 have all : (List.finRange 10).all (fun i => (northRegion i).all (fun c => decide (c∈soko1_2.board.floor)))=true := by decide +kernel
 intro c found
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c found)
theorem north_closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid :=
 FastCorral11.closed_of_checks _ _ _ _ _ reverse_checked north_floor north_checked
theorem north_unique : ∀ i, (northLocks i).Nodup := by decide +kernel
theorem north_size : ∀ i, (northLocks i).length=13 := by decide +kernel
#print axioms north_closed
theorem ring_checked (i : Fin 4) : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes ringLocks ringRegion ringPaid i=true := by
 obtain ⟨i,h⟩ := i
 have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
 rcases choices with rfl|rfl|rfl|rfl
 · exact ring0
 · exact ring1
 · exact ring2
 · exact ring3
theorem ring_tagged (i : Fin 4) : tagPart ringLocks ringRegion ringPaid ringAllowed i=true := by
 obtain ⟨i,h⟩ := i
 have choices : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
 rcases choices with rfl|rfl|rfl|rfl
 · exact ring0_tags
 · exact ring1_tags
 · exact ring2_tags
 · exact ring3_tags
theorem ring_floor (i : Fin 4) : ringRegion i⊆soko1_2.board.floor := by
 have all : (List.finRange 4).all (fun i => (ringRegion i).all (fun c => decide (c∈soko1_2.board.floor)))=true := by decide +kernel
 intro c found
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c found)
theorem ring_closed : PricedCorral11.ClosedExcept soko1_2.board soko1_2.initial.holes ringLocks ringRegion ringPaid :=
 FastCorral11.closed_of_checks _ _ _ _ _ reverse_checked ring_floor ring_checked
theorem ring_unique : ∀ i, (ringLocks i).Nodup := by decide +kernel
theorem ring_size : ∀ i, (ringLocks i).length=12 := by decide +kernel
#print axioms ring_closed
end Owner1007.PreCage12
