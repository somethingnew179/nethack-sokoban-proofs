import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0578_0_checked : (List.range' 295936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0578_1_checked : (List.range' 296064 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0578_2_checked : (List.range' 296192 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0578_3_checked : (List.range' 296320 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0578_range (index : Nat) (lower : 295936 ≤ index) (upper : index < 296448) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 296192 then
    if cut : index < 296064 then
      exact segment_sound _ 295936 128 Update0578_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 296064 128 Update0578_1_checked index (by omega) (by omega)
  else
    if cut : index < 296320 then
      exact segment_sound _ 296192 128 Update0578_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 296320 128 Update0578_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
