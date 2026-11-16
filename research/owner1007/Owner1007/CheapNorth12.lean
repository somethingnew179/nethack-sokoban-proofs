import Owner1007.FirstSplit12
import Owner1007.EastPrice225

namespace Owner1007.CheapNorth12
open NetHack.Sokoban

/-- Every original completion below225 must take the north first-push branch.
This removes arbitrary initial walking without changing the push count. -/
theorem all_cheap_completions_start_north {dirs final pushes moves}
    (trace : Trace soko1_2.board soko1_2.initial dirs final pushes moves)
    (completed : Goal final) (cheap : pushes ≤ 224) :
    ∃ suffixPushes suffixMoves suffixDirs,
      pushes = 1 + suffixPushes ∧
      Trace soko1_2.board FirstSplit12.afterN suffixDirs final suffixPushes suffixMoves := by
  obtain ⟨p, m, ds, count, north | east⟩ := FirstSplit12.original_first_push_split trace completed
  · exact ⟨p, m, ds, count, north⟩
  · have bound := EastPrice225.east_branch_225 east completed
    omega

#print axioms all_cheap_completions_start_north
end Owner1007.CheapNorth12
