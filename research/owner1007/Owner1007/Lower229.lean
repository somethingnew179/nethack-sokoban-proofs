import Owner1007.North22912
import Owner1007.East22912
namespace Owner1007.Lower229
open NetHack.Sokoban
open Owner1007.TokenAccounting
/-- Every completion of the unchanged full canonical map needs229 initiated pushes. -/
theorem pushes_lower_bound {dirs final pushes moves}
 (trace : Trace soko1_2.board soko1_2.initial dirs final pushes moves)
 (completed : Goal final) : 229≤pushes := by
 obtain ⟨q,m,ds,count,branch⟩ := FirstSplit12.original_first_push_split trace completed
 rcases branch with north|east
 · have bound := North22912.north_branch_229 north completed
   omega
 · have bound := East22912.east_branch_229 east completed
   omega
#print axioms pushes_lower_bound
end Owner1007.Lower229
