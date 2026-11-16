import Owner1007.Budget327B4Activation11
import Owner1007.RightParkedInduction11
namespace Owner1007.Budget327B4Impossible11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open Owner1007.TokenAccounting
/-- The actual original327 trace necessarily reaches one of four impossible frames. -/
theorem impossible {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327) : False := by
 apply Budget327B4Activation11.impossible ?_ logged completed cheap
 intro beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes first last i ready
 exact RightParkedInduction11.impossible first last i ready
#print axioms impossible
end Owner1007.Budget327B4Impossible11
