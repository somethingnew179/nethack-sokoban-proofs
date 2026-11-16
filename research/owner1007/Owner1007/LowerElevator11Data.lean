import Owner1007.FastCorral11
import Owner1007.ZeroWord11
namespace Owner1007.LowerElevator11
open NetHack.Sokoban
def locks (i : Fin 4) : List Cell := match i.val with
 | 0 =>[266,292,317]
 | 1 =>[265,292,317]
 | 2 =>[266,291,317]
 | 3 =>[265,291,317]
 | _=>[]
def region (i : Fin 4) : List Cell := match i.val with
 | 0 =>[267,268,269,270,271,293,294,295,296,297,318,319,320,321,322,345,365,366,367,368,369,370,371,372,391,392,393,394,395,396,397,398,417,418,419]
 | 1 =>[266,267,268,269,270,271,293,294,295,296,297,318,319,320,321,322,345,365,366,367,368,369,370,371,372,391,392,393,394,395,396,397,398,417,418,419]
 | 2 =>[267,268,269,270,271,292,293,294,295,296,297,318,319,320,321,322,345,365,366,367,368,369,370,371,372,391,392,393,394,395,396,397,398,417,418,419]
 | 3 =>[266,267,268,269,270,271,292,293,294,295,296,297,318,319,320,321,322,345,365,366,367,368,369,370,371,372,391,392,393,394,395,396,397,398,417,418,419]
 | _=>[]
def positive (source : Cell) (dir : Dir) : Prop :=
 ((source=265∨source=291∨source=317) ∧dir=.west) ∨ (source=292 ∧dir=.south)
instance (source : Cell) (dir : Dir) : Decidable (positive source dir) := by unfold positive;infer_instance
def paid (source : Cell) (dir : Dir) : Prop := source=317 ∨ (source=292∧dir=.north) ∨positive source dir
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
def Shape (i : Fin 4) (source : Cell) (dir : Dir) : Prop := positive source dir ∨(i.val=1∧source=292∧dir=.north)
instance (i : Fin 4) (source : Cell) (dir : Dir) : Decidable (Shape i source dir) := by unfold Shape;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique (i : Fin 4) : (locks i).Nodup := by
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1∨i=2∨i=3 := by omega
 rcases choices with rfl|rfl|rfl|rfl <;> dsimp only [locks] <;> decide +kernel
theorem size (i : Fin 4) : (locks i).length=3 := by
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1∨i=2∨i=3 := by omega
 rcases choices with rfl|rfl|rfl|rfl <;> rfl
theorem floor (i : Fin 4) : region i⊆soko1_1.board.floor := by
 have all : (List.finRange 4).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c member)
end Owner1007.LowerElevator11
