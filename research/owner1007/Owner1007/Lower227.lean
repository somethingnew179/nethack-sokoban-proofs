import Owner1007.North22712
import Owner1007.East22712
namespace Owner1007.Lower227
open NetHack.Sokoban
open Owner1007.TokenAccounting

/-- Every canonical full original-map completion needs at least227 initiated pushes. -/
theorem pushes_lower_bound {dirs final pushes moves}
 (trace : Trace soko1_2.board soko1_2.initial dirs final pushes moves)
 (completed : Goal final) : 227≤pushes := by
 obtain ⟨q,m,ds,count,branch⟩ := FirstSplit12.original_first_push_split trace completed
 rcases branch with north | east
 · obtain ⟨outcomes,logged⟩ := log_exists north (by decide +kernel)
   have bound := North22712.canonical_bound logged completed
   omega
 · have bound := East22712.east_branch_227 east completed
   omega
#print axioms pushes_lower_bound
end Owner1007.Lower227
