import Owner1007.North23112
import Owner1007.East23112
namespace Owner1007.Lower231
open NetHack.Sokoban
open Owner1007.TokenAccounting
/-- Every completion of the unchanged full canonical map needs231 initiated pushes. -/
theorem pushes_lower_bound {dirs final pushes moves}
 (trace : Trace soko1_2.board soko1_2.initial dirs final pushes moves)
 (completed : Goal final) : 231≤pushes := by
 obtain ⟨q,m,ds,count,branch⟩ := FirstSplit12.original_first_push_split trace completed
 rcases branch with north|east
 · have bound := North23112.north_branch_231 north completed
   omega
 · have bound := East23112.east_branch_231 east completed
   omega
#print axioms pushes_lower_bound
end Owner1007.Lower231
