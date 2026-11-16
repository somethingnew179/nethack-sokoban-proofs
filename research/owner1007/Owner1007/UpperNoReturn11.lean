import Owner1007.UpperZero11
namespace Owner1007.UpperNoReturn11
open NetHack.Sokoban

def sources : List Cell := [137,139,191,138,164,190,216,112]
def noReturnCheck (source : Cell) (dir : Dir) : Bool :=
  if dir.diagonal then true else if UpperZero11.paid source dir then true else
    (pushTargets soko1_1.board source dir).all fun dest => decide (dest≠137 ∧ dest≠139 ∧ dest≠191)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem all_checked : sources.all (fun source => allDirs.all (noReturnCheck source)) = true := by decide +kernel
theorem source_known (i : Fin 19) (source : Cell) (member : source ∈ UpperZero11.locks i) : source ∈ sources := by
  have all : (List.finRange 19).all (fun i => (UpperZero11.locks i).all (fun source => decide (source∈sources))) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp all i (by simp)) source member)
theorem landing_avoids (i : Fin 19) (source dest : Cell) (dir : Dir)
    (member : source ∈ UpperZero11.locks i) (cardinal : dir.diagonal=false)
    (unpaid : ¬ UpperZero11.paid source dir) (target : dest ∈ pushTargets soko1_1.board source dir) :
    dest≠137 ∧ dest≠139 ∧ dest≠191 := by
  have row := List.all_eq_true.mp (List.all_eq_true.mp all_checked source (source_known i source member)) dir
    (Geometry.all_directions dir)
  simp only [noReturnCheck,cardinal,Bool.false_eq_true,↓reduceIte,if_neg unpaid] at row
  exact of_decide_eq_true (List.all_eq_true.mp row dest target)
#print axioms all_checked
#print axioms landing_avoids
end Owner1007.UpperNoReturn11
