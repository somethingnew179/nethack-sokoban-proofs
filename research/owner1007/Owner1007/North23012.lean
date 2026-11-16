import Owner1007.NorthTwoJImpossibleEight12
import Owner1007.NorthTwoJ22912
import Owner1007.North211Tight22912
namespace Owner1007.North23012
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem impossible {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤229) : False := by
 obtain ⟨first,⟨second⟩⟩ := NorthTwoJ22912.canonical logged completed cheap
 have eight := (North211Tight22912.canonical_ledgers logged completed cheap).2.1
 exact NorthTwoJImpossibleEight12.impossible logged completed eight first second
theorem north_branch_230 {dirs final pushes moves}
 (trace : Trace soko1_2.board FirstSplit12.afterN dirs final pushes moves)
 (completed : Goal final) :230≤1+pushes := by
 apply Classical.byContradiction
 intro wrong
 have cheap : 1+pushes≤229 := by omega
 obtain ⟨outcomes,logged⟩ := log_exists trace (by decide +kernel)
 exact impossible logged completed cheap
#print axioms impossible
#print axioms north_branch_230
end Owner1007.North23012
