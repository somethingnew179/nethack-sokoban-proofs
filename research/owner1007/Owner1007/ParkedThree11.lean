import Owner1007.ParkedThree11Check00
import Owner1007.ParkedThree11Check01
import Owner1007.ParkedThree11Check02
import Owner1007.ParkedThree11Check03
import Owner1007.ParkedThree11Check04
import Owner1007.ParkedThree11Check05
import Owner1007.ParkedThree11Check06
import Owner1007.ParkedThree11Check07
import Owner1007.ParkedThree11Check08
import Owner1007.ParkedStrict11
import Owner1007.Hero315Frame11
import Owner1007.OwnedCorral11
import NetHack.Sokoban.Reduction
namespace Owner1007.ParkedThree11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked (i : Fin 9) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true := by
 obtain ⟨i,bound⟩ := i
 have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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

theorem floors (i : Fin 9) : region i⊆soko1_1.board.floor := by
 have all : (List.finRange 9).all (fun i => (region i).all (fun c => decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c found
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c found)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floors checked
#print axioms closed

theorem future_energy {state final : State} {history dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (group : List Cell) (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤3)
 (good : OwnedCorral11.Good locks region state group) :
 2≤Hero315Frame11.energy state final group outcomes := by
 by_cases enough : 2≤Hero315Frame11.energy state final group outcomes
 · exact enough
 · have cheap : Hero315Frame11.energy state final group outcomes<2 := by omega
   have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
   have priced : ∀ state dir t outcome group,
     HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state →
     group.Nodup → group⊆state.boulders → group.length≤3 →
     step soko1_1.board state dir=some t → Matches state t outcome →
     OwnedCorral11.PaidStep paid group dir t →
     2≤charge (Hero315Frame11.groupCertificate 3).holeWeight group outcome +
       (Hero315Frame11.groupCertificate 3).groupValue t.state (update group outcome) -
       (Hero315Frame11.groupCertificate 3).groupValue state group := by
     intro state dir t outcome group valid unique inside bounded checked effect pays
     obtain ⟨source,owner,metadata,pays⟩ := pays
     exact ParkedStrict11.exit_row Hero315Frame11.scalar rfl valid checked effect unique inside ⟨source,owner,metadata,pays⟩
   have persists := OwnedCorral11.small_energy_good closed unique size
     (Hero315Frame11.groupCertificate 3) 2 priced logged valid group groupUnique inside bounded good reached.holes_sublist.subset cheap
   obtain ⟨i,_,selected⟩ := persists
   have finalSubset := (logged.end_subset valid.1 group groupUnique inside).2
   have actual : locks i⊆final.boulders := List.Subset.trans selected finalSubset
   have card := List.Nodup.length_le_of_subset (unique i) actual
   rw [size i] at card
   have conservation := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   rw [empty] at conservation
   change 18+0=final.boulders.length+16 at conservation
   omega
#print axioms future_energy

end Owner1007.ParkedThree11
