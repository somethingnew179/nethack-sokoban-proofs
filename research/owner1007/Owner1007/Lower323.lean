import Owner1007.UpperReserve11
namespace Owner1007.Lower323
open NetHack.Sokoban
open Owner1007.TokenAccounting
/-- Universal bound from the canonical original full soko1-1 state. -/
theorem pushes_lower_bound {dirs final pushes moves}
 (trace : Trace soko1_1.board soko1_1.initial dirs final pushes moves) (completed : Goal final) :
 323≤pushes := by
 obtain ⟨outcomes,logged⟩ := log_exists trace (by decide +kernel)
 exact UpperBudget11.upper_suffices logged completed (UpperReserve11.upper_four logged completed)
#print axioms pushes_lower_bound
end Owner1007.Lower323
