import Owner1007.FastCorral11
import Owner1007.ZeroWord11
namespace Owner1007.Shaft18711
open NetHack.Sokoban
def locks (i : Fin 6) : List Cell := match i.val with
 | 0 =>[265,266]
 | 1 =>[239,266]
 | 2 =>[213,266]
 | 3 =>[239,265]
 | 4 =>[213,265]
 | 5 =>[213,239]
 | _=>[]
def region (i : Fin 6) : List Cell := match i.val with
 | 0 =>[262,263,264,267,268,269,270,271,288,289,290,291,292,293,294,295,296,297,314,315,316,317,318,319,320,321,322,345,365,366,367,368,369,370,371,372,391,392,393,394,395,396,397,398,417,418,419]
 | 1 =>[262,263,264,265,267,268,269,270,271,288,289,290,291,292,293,294,295,296,297,314,315,316,317,318,319,320,321,322,345,365,366,367,368,369,370,371,372,391,392,393,394,395,396,397,398,417,418,419]
 | 2 =>[239,262,263,264,265,267,268,269,270,271,288,289,290,291,292,293,294,295,296,297,314,315,316,317,318,319,320,321,322,345,365,366,367,368,369,370,371,372,391,392,393,394,395,396,397,398,417,418,419]
 | 3 =>[262,263,264,266,267,268,269,270,271,288,289,290,291,292,293,294,295,296,297,314,315,316,317,318,319,320,321,322,345,365,366,367,368,369,370,371,372,391,392,393,394,395,396,397,398,417,418,419]
 | 4 =>[262,263,264,266,267,268,269,270,271,288,289,290,291,292,293,294,295,296,297,314,315,316,317,318,319,320,321,322,345,365,366,367,368,369,370,371,372,391,392,393,394,395,396,397,398,417,418,419]
 | 5 =>[262,263,264,265,266,267,268,269,270,271,288,289,290,291,292,293,294,295,296,297,314,315,316,317,318,319,320,321,322,345,365,366,367,368,369,370,371,372,391,392,393,394,395,396,397,398,417,418,419]
 | _=>[]
def positive (source : Cell) (dir : Dir) : Prop :=
 (source=265 ∧(dir=.east∨dir=.west)) ∨ (source=266∧dir=.east)
instance (source : Cell) (dir : Dir) : Decidable (positive source dir) := by unfold positive;infer_instance
def paid (source : Cell) (dir : Dir) : Prop := (source=213∧dir=.north) ∨positive source dir
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
def Shape (i : Fin 6) (source : Cell) (dir : Dir) : Prop := positive source dir ∨(i.val=2∧source=213∧dir=.north)
instance (i : Fin 6) (source : Cell) (dir : Dir) : Decidable (Shape i source dir) := by unfold Shape;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique (i : Fin 6) : (locks i).Nodup := by
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1∨i=2∨i=3∨i=4∨i=5 := by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only [locks] <;> decide +kernel
theorem size (i : Fin 6) : (locks i).length=2 := by
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1∨i=2∨i=3∨i=4∨i=5 := by omega
 rcases choices with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
theorem floor (i : Fin 6) : region i⊆soko1_1.board.floor := by
 have all : (List.finRange 6).all (fun i=>(region i).all (fun c=>decide (c∈soko1_1.board.floor)))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) c member)
end Owner1007.Shaft18711
