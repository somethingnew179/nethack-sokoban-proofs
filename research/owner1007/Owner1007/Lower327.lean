import Owner1007.Cycle32611
namespace Owner1007.Lower327
open NetHack.Sokoban
open Owner1007.TokenAccounting
/-- Initiated pushes from the unchanged full original canonical map. -/
theorem pushes_lower_bound {dirs final pushes moves}
 (trace : Trace soko1_1.board soko1_1.initial dirs final pushes moves) (completed : Goal final) :
 327≤pushes := by
 apply Nat.le_of_not_gt
 intro short
 have cheap : pushes≤326 := by omega
 obtain ⟨outcomes,logged⟩ := log_exists trace (by decide +kernel)
 exact Cycle32611.impossible logged completed cheap
#print axioms pushes_lower_bound
end Owner1007.Lower327
