import Owner1007.StationaryGuardsSix11
import Owner1007.StationaryExit11
import Owner1007.HeroEnergyTrace11
namespace Owner1007.StationaryExitSix11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11

theorem survives139 {beforeDirs middle beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_1.board middle .east=some t) (effect : Matches middle t (.push 139 (.stay 140)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (stationary : ownPushes [139] before=0)
 (cheap : energy soko1_1.initial middle [141] before<6) :
 endGroup [139] (before ++ .push 139 (.stay 140) :: after)≠[] :=
 StationaryExit11.after_push_survives first checked effect last (by decide +kernel) (by decide +kernel)
   (by decide) (no_push_unchanged _ _ stationary) (StationaryGuardsSix11.guard141 first stationary cheap)
   (Owner1007.locked_of_check _ _ (by decide +kernel)) (by decide +kernel)

theorem survives191 {beforeDirs middle beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_1.board middle .east=some t) (effect : Matches middle t (.push 191 (.stay 192)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (stationary : ownPushes [191] before=0)
 (cheap : energy soko1_1.initial middle [193] before<6) :
 endGroup [191] (before ++ .push 191 (.stay 192) :: after)≠[] :=
 StationaryExit11.after_push_survives first checked effect last (by decide +kernel) (by decide +kernel)
   (by decide) (no_push_unchanged _ _ stationary) (StationaryGuardsSix11.guard193 first stationary cheap)
   (Owner1007.locked_of_check _ _ (by decide +kernel)) (by decide +kernel)

#print axioms survives139
#print axioms survives191
end Owner1007.StationaryExitSix11
