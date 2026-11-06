import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0701_0_checked : (List.range' 358912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0701_1_checked : (List.range' 359040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0701_2_checked : (List.range' 359168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0701_3_checked : (List.range' 359296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0701_range (index : Nat) (lower : 358912 ≤ index) (upper : index < 359424) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 359168 then
    if cut : index < 359040 then
      exact segment_sound _ 358912 128 Update0701_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 359040 128 Update0701_1_checked index (by omega) (by omega)
  else
    if cut : index < 359296 then
      exact segment_sound _ 359168 128 Update0701_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 359296 128 Update0701_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
