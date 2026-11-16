import Owner1007.LowerElevator11Geometry
import Owner1007.Gate265Transport11
import Owner1007.Gate265Above11Data
import Owner1007.WestRankHead11
namespace Owner1007.AboveOther11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def G : List Cell := [266,268,293,317,321]
def locks (i : Fin 3) : List Cell := G++[if i.val=0 then 265 else if i.val=1 then 291 else 292]
def region (i : Fin 3) : List Cell := if i.val=0 then Gate265Transport11.upper else
 soko1_1.board.floor.filter fun c=>!((LowerElevator11.region (if i.val=1 then 2 else 0)++locks i).contains c)
def paid (source : Cell) (_ : Dir) : Prop := source∈G
instance (c : Cell) (d : Dir) : Decidable (paid c d) := by unfold paid;infer_instance
theorem unique : ∀i,(locks i).Nodup := by decide +kernel
theorem size : ∀i,(locks i).length=6 := by decide +kernel
theorem floor (i : Fin 3) : region i⊆soko1_1.board.floor := by
 intro c h
 unfold region at h
 split at h
 ·exact Gate265Above11.floor 0 h
 ·exact (List.mem_filter.mp h).1

def Shape (source : Cell) (dir : Dir) : Prop := (source=266∧dir=.east)∨(source=317∧dir=.east)
instance (c : Cell) (d : Dir) : Decidable (Shape c d) := by unfold Shape;infer_instance
def headCheck (i : Fin 3) : Bool := G.all fun source=>allDirs.all fun dir=>
 match advance soko1_1.board source dir.opposite with
 |none=>true
 |some hero=>decide (hero∉region i ∨BlockedPush soko1_1.board (locks i) source dir ∨Shape source dir)
theorem heads : (List.finRange 3).all headCheck=true := by decide +kernel

theorem head_shape {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (i : Fin 3) (hero : state.player∈region i) (inside : locks i⊆state.boulders)
 (member : source∈G) (checked : step soko1_1.board state dir=some t) (metadata : t.pushSource=some source) : Shape source dir := by
 have row := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp heads i (by simp)) source member) dir (Geometry.all_directions dir)
 have adjacent := PairPost11.source_adjacent checked metadata
 have behind := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor i hero) dir source adjacent
 simp only [headCheck,behind] at row
 exact ((of_decide_eq_true row).resolve_left (fun h=>h hero)).resolve_left (WestRankHead11.source_unblocked checked metadata inside)
#print axioms heads
#print axioms head_shape
end Owner1007.AboveOther11
