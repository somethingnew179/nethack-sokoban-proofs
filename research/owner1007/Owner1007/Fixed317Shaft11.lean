import Owner1007.Fixed317Shaft11Check0
import Owner1007.Fixed317Shaft11Check1
import Owner1007.Fixed317Shaft11Check2
import Owner1007.Fixed317Shaft11Check3
import Owner1007.Fixed317Shaft11Check4
import Owner1007.Fixed317Shaft11Check5
import Owner1007.Fixed317Shaft11Check6
import Owner1007.Fixed317Shaft11Check7
namespace Owner1007.Fixed317Shaft11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked (i : Fin 8) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true := by
 obtain ⟨v,bound⟩ := i
 have cases : v=0∨v=1∨v=2∨v=3∨v=4∨v=5∨v=6∨v=7 := by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir with
     | north => exact w0_0
     | south => exact w0_1
     | east => exact w0_2
     | west => exact w0_3
     | northEast => exact w0_4
     | northWest => exact w0_5
     | southEast => exact w0_6
     | southWest => exact w0_7
   · exact p0
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir with
     | north => exact w1_0
     | south => exact w1_1
     | east => exact w1_2
     | west => exact w1_3
     | northEast => exact w1_4
     | northWest => exact w1_5
     | southEast => exact w1_6
     | southWest => exact w1_7
   · exact p1
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir with
     | north => exact w2_0
     | south => exact w2_1
     | east => exact w2_2
     | west => exact w2_3
     | northEast => exact w2_4
     | northWest => exact w2_5
     | southEast => exact w2_6
     | southWest => exact w2_7
   · exact p2
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir with
     | north => exact w3_0
     | south => exact w3_1
     | east => exact w3_2
     | west => exact w3_3
     | northEast => exact w3_4
     | northWest => exact w3_5
     | southEast => exact w3_6
     | southWest => exact w3_7
   · exact p3
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir with
     | north => exact w4_0
     | south => exact w4_1
     | east => exact w4_2
     | west => exact w4_3
     | northEast => exact w4_4
     | northWest => exact w4_5
     | southEast => exact w4_6
     | southWest => exact w4_7
   · exact p4
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir with
     | north => exact w5_0
     | south => exact w5_1
     | east => exact w5_2
     | west => exact w5_3
     | northEast => exact w5_4
     | northWest => exact w5_5
     | southEast => exact w5_6
     | southWest => exact w5_7
   · exact p5
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir with
     | north => exact w6_0
     | south => exact w6_1
     | east => exact w6_2
     | west => exact w6_3
     | northEast => exact w6_4
     | northWest => exact w6_5
     | southEast => exact w6_6
     | southWest => exact w6_7
   · exact p6
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir with
     | north => exact w7_0
     | south => exact w7_1
     | east => exact w7_2
     | west => exact w7_3
     | northEast => exact w7_4
     | northWest => exact w7_5
     | southEast => exact w7_6
     | southWest => exact w7_7
   · exact p7
theorem floors : ∀ i, region i⊆soko1_1.board.floor := by
 have all : H.all (fun c=>decide (c∈soko1_1.board.floor))=true := by decide +kernel
 intro i c member
 have inside : c∈H := by
   unfold region at member
   split at member <;> exact (List.mem_filter.mp member).1
 exact of_decide_eq_true (List.all_eq_true.mp all c inside)
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem size : ∀ i, (locks i).length=2 := by intro i; rfl
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floors checked
#print axioms checked
#print axioms closed
#print axioms unique
#print axioms size
end Owner1007.Fixed317Shaft11
