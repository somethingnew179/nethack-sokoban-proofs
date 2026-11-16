import Owner1007.North265Eight12
import Owner1007.NorthReserveCount12
namespace Owner1007.North265Count12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
abbrev p := Generated.soko1_2Potential
theorem first265_lower226 {dirs final pushes moves outcomes}
    (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
    (completed : Goal final)
    {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
    (shape : outcomes=before ++ .push 265 (.stay 291) :: after)
    (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
    (checked : step soko1_2.board middle .south=some t)
    (effect : Matches middle t (.push 265 (.stay 291)))
    (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
    (i : Fin 5) (locksInside : NorthEvents12.locks i ⊆ endGroup NorthBound12.G before) :
    226≤1+pushes := by
 have lower := North265Eight12.first265_eight logged completed shape first checked effect last i locksInside
 exact NorthReserveCount12.canonical_bound logged completed 8 lower
#print axioms first265_lower226
end Owner1007.North265Count12
