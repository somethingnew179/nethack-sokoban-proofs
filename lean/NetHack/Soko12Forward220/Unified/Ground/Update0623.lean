import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0623_0_checked : (List.range' 318976 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0623_1_checked : (List.range' 319104 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0623_2_checked : (List.range' 319232 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0623_3_checked : (List.range' 319360 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0623_range (index : Nat) (lower : 318976 ≤ index) (upper : index < 319488) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 319232 then
    if cut : index < 319104 then
      exact segment_sound _ 318976 128 Update0623_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 319104 128 Update0623_1_checked index (by omega) (by omega)
  else
    if cut : index < 319360 then
      exact segment_sound _ 319232 128 Update0623_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 319360 128 Update0623_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
