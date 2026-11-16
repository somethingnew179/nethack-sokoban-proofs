import Owner1007.Paid137Six11
import Owner1007.UpperEastSix11
import Owner1007.Upper138WestSix11
import Owner1007.Upper138EastSix11
import Owner1007.Upper190EastSix11
import Owner1007.Upper190WestSix11
import Owner1007.Upper216Six11
import Owner1007.UpperHeadCases11
namespace Owner1007.UpperUniversalSix11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11
/-- Every original canonical completion pays six units for the six upper identities.
The eight cases are actual first paid events, with arbitrary interleaved moves. -/
theorem upper_six {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) : 6≤energy soko1_1.initial final U6 outcomes := by
 obtain ⟨cut⟩ := first_cut logged completed
 rcases UpperHeadCases11.FirstCut.head_cases cut with
   ⟨directionEq,sourceEq,headEq⟩ | ⟨directionEq,sourceEq,headEq⟩ | ⟨directionEq,sourceEq,headEq⟩ |
   ⟨directionEq,sourceEq,headEq⟩ | ⟨directionEq,sourceEq,headEq⟩ | ⟨directionEq,sourceEq,headEq⟩ |
   ⟨directionEq,sourceEq,headEq⟩ | ⟨directionEq,sourceEq,headEq⟩
 · exact Paid137Six11.upper_six logged completed (UpperEventEnergy11.original137_two cut sourceEq directionEq)
 · exact UpperEastSix11.reserve139_six logged completed cut directionEq sourceEq headEq
 · exact UpperEastSix11.reserve191_six logged completed cut directionEq sourceEq headEq
 · apply Upper138EastSix11.upper_six logged completed cut sourceEq directionEq
   simpa only [headEq] using cut.headEffect
 · apply Upper138WestSix11.upper_six logged completed cut sourceEq directionEq
   simpa only [headEq] using cut.headEffect
 · apply Upper190EastSix11.upper_six logged completed cut sourceEq directionEq
   simpa only [headEq] using cut.headEffect
 · apply Upper190WestSix11.upper_six logged completed cut sourceEq directionEq
   simpa only [headEq] using cut.headEffect
 · exact Upper216Six11.reserve_six logged completed cut sourceEq headEq
#print axioms upper_six
end Owner1007.UpperUniversalSix11
