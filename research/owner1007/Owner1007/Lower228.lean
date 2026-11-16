import Owner1007.North22812
import Owner1007.East22912
namespace Owner1007.Lower228
open NetHack.Sokoban
open Owner1007.TokenAccounting

/-- Every canonical full original-map completion needs at least227 initiated pushes. -/
theorem pushes_lower_bound {dirs final pushes moves}
 (trace : Trace soko1_2.board soko1_2.initial dirs final pushes moves)
 (completed : Goal final) : 228≤pushes := by
 obtain ⟨q,m,ds,count,branch⟩ := FirstSplit12.original_first_push_split trace completed
 rcases branch with north | east
 · obtain ⟨outcomes,logged⟩ := log_exists north (by decide +kernel)
   have bound := North22812.canonical_bound logged completed
   omega
 · have bound := East22912.east_branch_229 east completed
   omega
#print axioms pushes_lower_bound
end Owner1007.Lower228
