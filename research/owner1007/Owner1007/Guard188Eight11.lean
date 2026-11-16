import Owner1007.Guard188Eight11Check00
import Owner1007.Guard188Eight11Check01
import Owner1007.Guard188Eight11Check02
import Owner1007.Guard188Eight11Check03
import Owner1007.Guard188Eight11Check04
import Owner1007.Guard188Eight11Check05
import Owner1007.Guard188Eight11Check06
import Owner1007.Guard188Eight11Check07
import Owner1007.RankedCorral11
namespace Owner1007.Guard188Eight11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked (i : Fin 8) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true := by
 obtain ⟨i,bound⟩ := i
 have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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

theorem floors (i : Fin 8) : region i⊆soko1_1.board.floor := by
 have all : (List.finRange 8).all (fun i => (region i).all (fun c => decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c found
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c found)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floors checked
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def landingCheck : Bool := ([187,191] : List Cell).all fun c => (List.finRange 8).all fun i =>
 (locks i).all fun source => allDirs.all fun dir =>
 (pushTargets soko1_1.board source dir).all fun target =>
 decide (dir.diagonal=false → target=c → UpperLocalPrice11.paid source dir)
theorem landing_checked : landingCheck=true := by decide +kernel

theorem lock_complete (i : Fin 8) (group : List Cell) (bounded : group.length≤3)
 (inside : locks i⊆group) (source : Cell) (owner : source∈group) : source∈locks i := by
 by_cases member : source∈locks i
 · exact member
 · have all : source::locks i⊆group := by
     intro c found
     rcases List.mem_cons.mp found with rfl|later
     · exact owner
     · exact inside later
   have card := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨member,unique i⟩) all
   simp only [List.length_cons,size i] at card
   omega

theorem priced_landing (c : Cell) (member : c∈[187,191]) (state : State) (dir : Dir) (t : Transition)
 (group : List Cell) (source target : Cell)
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state)
 (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤3)
 (good : OwnedCorral11.Good locks region state group)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t (.push source (.stay target)))
 (owner : source∈group) (same : target=c) :
 2≤RankedCorral11.gap state t group (.push source (.stay target)) := by
 obtain ⟨i,heroInside,locksInside⟩ := good
 have sourceInside := lock_complete i group bounded locksInside source owner
 obtain ⟨cardinal,landing⟩ := UpperQuiet11.stay_geometry head effect
 have a := List.all_eq_true.mp landing_checked c member
 have b := List.all_eq_true.mp (List.all_eq_true.mp a i (by simp)) source sourceInside
 have d := List.all_eq_true.mp b dir (Geometry.all_directions dir)
 have pays := of_decide_eq_true (List.all_eq_true.mp d target landing) cardinal same
 exact UpperLocalPrice11.exit_row valid groupUnique inside head effect ⟨source,owner,by rw [effect.2],pays⟩
#print axioms closed
#print axioms priced_landing

end Owner1007.Guard188Eight11
