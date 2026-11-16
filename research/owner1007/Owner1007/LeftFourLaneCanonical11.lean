import Owner1007.LeftFourLane11
import Owner1007.LeftFourLaneLabels11
import Owner1007.LeftFourLaneForward11
namespace Owner1007.LeftFourLaneCanonical11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
theorem at_forward
 {dirs final pushes moves outcomes}
 (cut : FirstCut RightEarlyWords11.paid soko1_1.initial RightEarlyWords11.G dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327)
 (cheapLeft : energy soko1_1.initial final [186] outcomes≤4)
 (cheapUpper : energy soko1_1.initial final UpperBudget11.U6 outcomes<8)
 (cheapRest : energy soko1_1.initial final UpperBudget11.Rest outcomes<2)
 (source190 : cut.actor.pushSource=some 190) (west : cut.direction=.west)
 (head190 : cut.headOutcome=.push 190 (.stay 189))
 (tag191 : endGroup [191] cut.beforeOutcomes=[190]) :
 (endGroup [186] cut.beforeOutcomes=[184]∧endGroup [188] cut.beforeOutcomes=[186])∨
 (endGroup [186] cut.beforeOutcomes=[184]∧endGroup [188] cut.beforeOutcomes=[187])∨
 (endGroup [186] cut.beforeOutcomes=[185]∧endGroup [188] cut.beforeOutcomes=[187]) :=
 LeftFourLaneForward11.at_forward LeftFourLane11.closed LeftFourLane11.refined
  cut completed cheap cheapLeft cheapUpper cheapRest source190 west head190 tag191
#print axioms at_forward
end Owner1007.LeftFourLaneCanonical11
