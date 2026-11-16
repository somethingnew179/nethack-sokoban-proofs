import Owner1007.NorthTwoJImpossible12
import Owner1007.NorthTwoJ22812
namespace Owner1007.North22912
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem impossible {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤228) : False := by
 obtain ⟨first,⟨second⟩⟩ := NorthTwoJ22812.canonical logged completed cheap
 exact NorthTwoJImpossible12.impossible logged completed cheap first second
theorem north_branch_229 {dirs final pushes moves}
 (trace : Trace soko1_2.board FirstSplit12.afterN dirs final pushes moves)
 (completed : Goal final) :229≤1+pushes := by
 apply Classical.byContradiction
 intro wrong
 have cheap : 1+pushes≤228 := by omega
 obtain ⟨outcomes,logged⟩ := log_exists trace (by decide +kernel)
 exact impossible logged completed cheap
#print axioms impossible
#print axioms north_branch_229
end Owner1007.North22912
