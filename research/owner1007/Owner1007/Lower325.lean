import Owner1007.UpperUniversalSix11
namespace Owner1007.Lower325
open NetHack.Sokoban
open Owner1007.TokenAccounting
/-- Universal lower bound for initiated pushes from the full original canonical state. -/
theorem pushes_lower_bound {dirs final pushes moves}
 (trace : Trace soko1_1.board soko1_1.initial dirs final pushes moves) (completed : Goal final) :
 325≤pushes := by
 obtain ⟨outcomes,logged⟩ := log_exists trace (by decide +kernel)
 exact UpperSixBudget11.six_suffices logged completed (UpperUniversalSix11.upper_six logged completed)
#print axioms pushes_lower_bound
end Owner1007.Lower325
