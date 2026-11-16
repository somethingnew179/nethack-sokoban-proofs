import Owner1007.StrongFirst137EastCore11
namespace Owner1007.Row13313513711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
theorem canonical_no_west
 {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t (.push 137 (.stay 136)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (stationary : ownPushes [137] before=0)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 (before++.push 137 (.stay 136)::after)≤8)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest (before++.push 137 (.stay 136)::after)≤4) : False :=
 canonical_no_west_with closed first head effect last completed stationary upperCap restCap
#print axioms canonical_no_west
end Owner1007.Row13313513711
namespace Owner1007.StrongFirst137East11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.First137East11
theorem chronological
 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 outcomes≤8)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest outcomes≤4) :
 ∃cut : FirstCut paid soko1_1.initial [137] dirs final pushes moves outcomes,
   cut.actor.pushSource=some 137 ∧ cut.direction=.east ∧ cut.headOutcome=.push 137 (.stay 138) ∧
   ownPushes [137] cut.beforeOutcomes=0 ∧ cut.middle.holes=soko1_1.initial.holes :=
 chronological_with Row13313513711.closed logged completed upperCap restCap
#print axioms chronological
end Owner1007.StrongFirst137East11
