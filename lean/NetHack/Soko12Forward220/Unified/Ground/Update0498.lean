import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0498_0_checked : (List.range' 254976 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0498_1_checked : (List.range' 255104 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0498_2_checked : (List.range' 255232 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0498_3_checked : (List.range' 255360 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0498_range (index : Nat) (lower : 254976 ≤ index) (upper : index < 255488) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 255232 then
    if cut : index < 255104 then
      exact segment_sound _ 254976 128 Update0498_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 255104 128 Update0498_1_checked index (by omega) (by omega)
  else
    if cut : index < 255360 then
      exact segment_sound _ 255232 128 Update0498_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 255360 128 Update0498_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
