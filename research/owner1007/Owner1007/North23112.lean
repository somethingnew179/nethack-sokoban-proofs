import Owner1007.NorthToS23012
import Owner1007.NorthS211Impossible23012
namespace Owner1007.North23112
open NetHack.Sokoban
open Owner1007.TokenAccounting
/-- No original north-first completion can use at most230 initiated pushes. -/
theorem impossible {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤230) : False := by
 obtain ⟨stage⟩:=NorthToS23012.canonical logged completed cheap
 exact NorthS211Impossible23012.impossible logged completed cheap stage

theorem north_branch_231 {dirs final pushes moves}
 (trace : Trace soko1_2.board FirstSplit12.afterN dirs final pushes moves)
 (completed : Goal final) : 231≤1+pushes := by
 obtain ⟨outcomes,logged⟩:=log_exists trace (by decide +kernel)
 by_cases enough : 231≤1+pushes
 ·exact enough
 ·exact False.elim (impossible logged completed (by omega))
#print axioms impossible
#print axioms north_branch_231
end Owner1007.North23112
