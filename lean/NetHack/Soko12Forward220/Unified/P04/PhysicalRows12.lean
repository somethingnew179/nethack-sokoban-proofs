import NetHack.Soko12Forward220.Unified.PhysicalCoverageCore
import NetHack.Soko12Forward220.Unified.P04.OracleCover64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban
theorem physicalRow768 : CoveredFor 4 400 .north :=
  row_covered 4 400 .north rowCases768 oracleCover768 rowFits768 rowChecked768 rowHero768 rowDirection768 rowPhase768
theorem physicalRow769 : CoveredFor 4 400 .south :=
  row_covered 4 400 .south rowCases769 oracleCover769 rowFits769 rowChecked769 rowHero769 rowDirection769 rowPhase769
theorem physicalRow770 : CoveredFor 4 400 .east :=
  row_covered 4 400 .east rowCases770 oracleCover770 rowFits770 rowChecked770 rowHero770 rowDirection770 rowPhase770
theorem physicalRow771 : CoveredFor 4 400 .west :=
  row_covered 4 400 .west rowCases771 oracleCover771 rowFits771 rowChecked771 rowHero771 rowDirection771 rowPhase771
theorem physicalRow772 : CoveredFor 4 400 .northEast :=
  row_covered 4 400 .northEast rowCases772 oracleCover772 rowFits772 rowChecked772 rowHero772 rowDirection772 rowPhase772
theorem physicalRow773 : CoveredFor 4 400 .northWest :=
  row_covered 4 400 .northWest rowCases773 oracleCover773 rowFits773 rowChecked773 rowHero773 rowDirection773 rowPhase773
theorem physicalRow774 : CoveredFor 4 400 .southEast :=
  row_covered 4 400 .southEast rowCases774 oracleCover774 rowFits774 rowChecked774 rowHero774 rowDirection774 rowPhase774
theorem physicalRow775 : CoveredFor 4 400 .southWest :=
  row_covered 4 400 .southWest rowCases775 oracleCover775 rowFits775 rowChecked775 rowHero775 rowDirection775 rowPhase775
end NetHack.Soko12Forward220.Unified.P04
