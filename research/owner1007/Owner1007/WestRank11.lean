import Owner1007.WestRank11Check00
import Owner1007.WestRank11Check01
import Owner1007.WestRank11Check02
import Owner1007.WestRank11Check03
import Owner1007.WestRank11Check04
import Owner1007.WestRank11Check05
import Owner1007.WestRank11Check06
import Owner1007.WestRank11Check07
import Owner1007.WestRank11Check08
import Owner1007.WestRank11Check09
import Owner1007.WestRank11Check10
import Owner1007.WestRank11Check11
import Owner1007.WestRank11Check12
import Owner1007.WestRank11Check13
import Owner1007.WestRank11Check14
import Owner1007.RankedCorral11
namespace Owner1007.WestRank11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked (i : Fin 15) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true := by
 obtain ⟨i,bound⟩ := i
 have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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

theorem refinement_checked (i : Fin 15) : refinementCheck i=true := by
 obtain ⟨i,bound⟩ := i
 have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact refine0
 · exact refine1
 · exact refine2
 · exact refine3
 · exact refine4
 · exact refine5
 · exact refine6
 · exact refine7
 · exact refine8
 · exact refine9
 · exact refine10
 · exact refine11
 · exact refine12
 · exact refine13
 · exact refine14

theorem floors (i : Fin 15) : region i⊆soko1_1.board.floor := by
 have all : (List.finRange 15).all (fun i => (region i).all (fun c => decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c found
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c found)
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floors checked

theorem refined : RankedCorral11.Refinement locks region marker rank paid := by
 intro i hero source dest dir j heroInside sourceInside adjacent cardinal unpaid target targets noHole nextLocks nextHero
 have row := List.all_eq_true.mp (List.all_eq_true.mp (refinement_checked i) source sourceInside) dir (Geometry.all_directions dir)
 have reverse := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (floors i heroInside) dir source adjacent
 simp only [reverse,if_pos heroInside] at row
 have numeric := List.all_eq_true.mp (List.all_eq_true.mp row j (by simp)) dest target
 exact of_decide_eq_true numeric cardinal unpaid targets noHole nextLocks nextHero

def ExitShape (i : Fin 15) (source : Cell) (dir : Dir) : Prop :=
 (source=136 ∧ dir=.west ∧ rank i=2) ∨ (source=139 ∧ dir=.east ∧ rank i=2) ∨
 (source=191 ∧ dir=.east) ∨ (source=216 ∧ dir=.east)
instance (i : Fin 15) (source : Cell) (dir : Dir) : Decidable (ExitShape i source dir) := by unfold ExitShape; infer_instance
def exitCheck (i : Fin 15) : Bool := (locks i).all fun source => allDirs.all fun dir =>
 match advance soko1_1.board source dir.opposite with
 | none => true
 | some hero => decide (hero∈region i → ¬BlockedPush soko1_1.board (locks i) source dir → paid source dir → ExitShape i source dir)
theorem exits_checked : (List.finRange 15).all exitCheck=true := by decide +kernel
theorem exit_shape (i : Fin 15) (hero source : Cell) (dir : Dir)
 (heroInside : hero∈region i) (sourceInside : source∈locks i) (adjacent : advance soko1_1.board hero dir=some source)
 (unblocked : ¬BlockedPush soko1_1.board (locks i) source dir) (pays : paid source dir) : ExitShape i source dir := by
 have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp exits_checked i (by simp)) source sourceInside) dir (Geometry.all_directions dir)
 have reverse := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked hero (floors i heroInside) dir source adjacent
 simp only [reverse] at row
 exact of_decide_eq_true row heroInside unblocked pays
#print axioms closed
#print axioms refined
#print axioms exit_shape

end Owner1007.WestRank11
