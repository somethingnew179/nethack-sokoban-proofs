import Owner1007.Upper187Cover11Check00
import Owner1007.Upper187Cover11Check01
import Owner1007.Upper187Cover11Check02
import Owner1007.Upper187Cover11Check03
import Owner1007.Upper187Cover11Check04
import Owner1007.Upper187Cover11Check05
import Owner1007.Upper187Cover11Check06
import Owner1007.Upper187Cover11Check07
import Owner1007.Upper187Cover11Check08
import Owner1007.Upper187Cover11Check09
import Owner1007.Upper187Cover11Check10
import Owner1007.Upper187Cover11Check11
import Owner1007.Upper187Cover11Check12
import Owner1007.Upper187Cover11Check13
import Owner1007.Upper187Cover11Check14
import Owner1007.Upper187Cover11Check15
import Owner1007.Upper187Cover11Check16
import Owner1007.Upper187Cover11Check17
import Owner1007.Upper187Cover11Check18
import Owner1007.Upper187Cover11Check19
import Owner1007.Upper187Cover11Check20
import Owner1007.Upper187Cover11Check21
import Owner1007.Upper187Cover11Check22
import Owner1007.Upper187Cover11Check23
import Owner1007.Upper187Cover11Check24
import Owner1007.Upper187Cover11Check25
import Owner1007.Upper187Cover11Check26
import Owner1007.Upper187Cover11Check27
import Owner1007.Upper187Cover11Check28
import Owner1007.Upper187Cover11Check29
import Owner1007.Upper187Cover11Check30
import Owner1007.Upper187Cover11Check31
import Owner1007.Upper187Cover11Check32
import Owner1007.Upper187Cover11Check33
import Owner1007.Upper187Cover11Check34
import Owner1007.Upper187Cover11Check35
import Owner1007.OwnedCorralAny11
namespace Owner1007.Upper187Cover11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked (i : Fin 36) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true := by
 obtain ⟨i,bound⟩ := i
 have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 := by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node0_north
     · exact node0_south
     · exact node0_east
     · exact node0_west
     · exact node0_northEast
     · exact node0_northWest
     · exact node0_southEast
     · exact node0_southWest
   · exact node0_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node1_north
     · exact node1_south
     · exact node1_east
     · exact node1_west
     · exact node1_northEast
     · exact node1_northWest
     · exact node1_southEast
     · exact node1_southWest
   · exact node1_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node2_north
     · exact node2_south
     · exact node2_east
     · exact node2_west
     · exact node2_northEast
     · exact node2_northWest
     · exact node2_southEast
     · exact node2_southWest
   · exact node2_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node3_north
     · exact node3_south
     · exact node3_east
     · exact node3_west
     · exact node3_northEast
     · exact node3_northWest
     · exact node3_southEast
     · exact node3_southWest
   · exact node3_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node4_north
     · exact node4_south
     · exact node4_east
     · exact node4_west
     · exact node4_northEast
     · exact node4_northWest
     · exact node4_southEast
     · exact node4_southWest
   · exact node4_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node5_north
     · exact node5_south
     · exact node5_east
     · exact node5_west
     · exact node5_northEast
     · exact node5_northWest
     · exact node5_southEast
     · exact node5_southWest
   · exact node5_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node6_north
     · exact node6_south
     · exact node6_east
     · exact node6_west
     · exact node6_northEast
     · exact node6_northWest
     · exact node6_southEast
     · exact node6_southWest
   · exact node6_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node7_north
     · exact node7_south
     · exact node7_east
     · exact node7_west
     · exact node7_northEast
     · exact node7_northWest
     · exact node7_southEast
     · exact node7_southWest
   · exact node7_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node8_north
     · exact node8_south
     · exact node8_east
     · exact node8_west
     · exact node8_northEast
     · exact node8_northWest
     · exact node8_southEast
     · exact node8_southWest
   · exact node8_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node9_north
     · exact node9_south
     · exact node9_east
     · exact node9_west
     · exact node9_northEast
     · exact node9_northWest
     · exact node9_southEast
     · exact node9_southWest
   · exact node9_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node10_north
     · exact node10_south
     · exact node10_east
     · exact node10_west
     · exact node10_northEast
     · exact node10_northWest
     · exact node10_southEast
     · exact node10_southWest
   · exact node10_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node11_north
     · exact node11_south
     · exact node11_east
     · exact node11_west
     · exact node11_northEast
     · exact node11_northWest
     · exact node11_southEast
     · exact node11_southWest
   · exact node11_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node12_north
     · exact node12_south
     · exact node12_east
     · exact node12_west
     · exact node12_northEast
     · exact node12_northWest
     · exact node12_southEast
     · exact node12_southWest
   · exact node12_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node13_north
     · exact node13_south
     · exact node13_east
     · exact node13_west
     · exact node13_northEast
     · exact node13_northWest
     · exact node13_southEast
     · exact node13_southWest
   · exact node13_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node14_north
     · exact node14_south
     · exact node14_east
     · exact node14_west
     · exact node14_northEast
     · exact node14_northWest
     · exact node14_southEast
     · exact node14_southWest
   · exact node14_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node15_north
     · exact node15_south
     · exact node15_east
     · exact node15_west
     · exact node15_northEast
     · exact node15_northWest
     · exact node15_southEast
     · exact node15_southWest
   · exact node15_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node16_north
     · exact node16_south
     · exact node16_east
     · exact node16_west
     · exact node16_northEast
     · exact node16_northWest
     · exact node16_southEast
     · exact node16_southWest
   · exact node16_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node17_north
     · exact node17_south
     · exact node17_east
     · exact node17_west
     · exact node17_northEast
     · exact node17_northWest
     · exact node17_southEast
     · exact node17_southWest
   · exact node17_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node18_north
     · exact node18_south
     · exact node18_east
     · exact node18_west
     · exact node18_northEast
     · exact node18_northWest
     · exact node18_southEast
     · exact node18_southWest
   · exact node18_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node19_north
     · exact node19_south
     · exact node19_east
     · exact node19_west
     · exact node19_northEast
     · exact node19_northWest
     · exact node19_southEast
     · exact node19_southWest
   · exact node19_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node20_north
     · exact node20_south
     · exact node20_east
     · exact node20_west
     · exact node20_northEast
     · exact node20_northWest
     · exact node20_southEast
     · exact node20_southWest
   · exact node20_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node21_north
     · exact node21_south
     · exact node21_east
     · exact node21_west
     · exact node21_northEast
     · exact node21_northWest
     · exact node21_southEast
     · exact node21_southWest
   · exact node21_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node22_north
     · exact node22_south
     · exact node22_east
     · exact node22_west
     · exact node22_northEast
     · exact node22_northWest
     · exact node22_southEast
     · exact node22_southWest
   · exact node22_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node23_north
     · exact node23_south
     · exact node23_east
     · exact node23_west
     · exact node23_northEast
     · exact node23_northWest
     · exact node23_southEast
     · exact node23_southWest
   · exact node23_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node24_north
     · exact node24_south
     · exact node24_east
     · exact node24_west
     · exact node24_northEast
     · exact node24_northWest
     · exact node24_southEast
     · exact node24_southWest
   · exact node24_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node25_north
     · exact node25_south
     · exact node25_east
     · exact node25_west
     · exact node25_northEast
     · exact node25_northWest
     · exact node25_southEast
     · exact node25_southWest
   · exact node25_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node26_north
     · exact node26_south
     · exact node26_east
     · exact node26_west
     · exact node26_northEast
     · exact node26_northWest
     · exact node26_southEast
     · exact node26_southWest
   · exact node26_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node27_north
     · exact node27_south
     · exact node27_east
     · exact node27_west
     · exact node27_northEast
     · exact node27_northWest
     · exact node27_southEast
     · exact node27_southWest
   · exact node27_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node28_north
     · exact node28_south
     · exact node28_east
     · exact node28_west
     · exact node28_northEast
     · exact node28_northWest
     · exact node28_southEast
     · exact node28_southWest
   · exact node28_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node29_north
     · exact node29_south
     · exact node29_east
     · exact node29_west
     · exact node29_northEast
     · exact node29_northWest
     · exact node29_southEast
     · exact node29_southWest
   · exact node29_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node30_north
     · exact node30_south
     · exact node30_east
     · exact node30_west
     · exact node30_northEast
     · exact node30_northWest
     · exact node30_southEast
     · exact node30_southWest
   · exact node30_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node31_north
     · exact node31_south
     · exact node31_east
     · exact node31_west
     · exact node31_northEast
     · exact node31_northWest
     · exact node31_southEast
     · exact node31_southWest
   · exact node31_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node32_north
     · exact node32_south
     · exact node32_east
     · exact node32_west
     · exact node32_northEast
     · exact node32_northWest
     · exact node32_southEast
     · exact node32_southWest
   · exact node32_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node33_north
     · exact node33_south
     · exact node33_east
     · exact node33_west
     · exact node33_northEast
     · exact node33_northWest
     · exact node33_southEast
     · exact node33_southWest
   · exact node33_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node34_north
     · exact node34_south
     · exact node34_east
     · exact node34_west
     · exact node34_northEast
     · exact node34_northWest
     · exact node34_southEast
     · exact node34_southWest
   · exact node34_push
 · apply FastCorral11.node_of_parts
   · intro dir
     cases dir
     · exact node35_north
     · exact node35_south
     · exact node35_east
     · exact node35_west
     · exact node35_northEast
     · exact node35_northWest
     · exact node35_southEast
     · exact node35_southWest
   · exact node35_push

theorem floors (i : Fin 36) : region i⊆soko1_1.board.floor := by
 have all : (List.finRange 36).all (fun i => (region i).all (fun c => decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c found
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c found)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floors checked

open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem future_energy {state final : State} {history dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (good : OwnedCorral11.Good locks region state group) (consumed : endGroup group outcomes=[]) :
 2≤energy state final group outcomes := by
 have priced : ∀state dir t outcome group,
   HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
   group.Nodup → group⊆state.boulders → group.length≤18 →
   step soko1_1.board state dir=some t → Matches state t outcome →
   OwnedCorral11.PaidStep paid group dir t →
   2≤charge (groupCertificate 18).holeWeight group outcome+
    (groupCertificate 18).groupValue t.state (update group outcome)-(groupCertificate 18).groupValue state group := by
   intro state dir t outcome group valid unique inside bounded head effect pays
   exact UpperLocalPrice11.exit_row valid unique inside head effect pays
 exact OwnedCorralAny11.energy_if_empty closed unique nonempty (groupCertificate 18) 2 priced logged
   (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached) group groupUnique inside bounded good reached.holes_sublist.subset consumed
#print axioms closed
#print axioms future_energy

end Owner1007.Upper187Cover11
