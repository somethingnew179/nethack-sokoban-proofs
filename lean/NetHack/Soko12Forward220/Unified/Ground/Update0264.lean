import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0264_0_checked : (List.range' 135168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0264_1_checked : (List.range' 135296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0264_2_checked : (List.range' 135424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0264_3_checked : (List.range' 135552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0264_range (index : Nat) (lower : 135168 ≤ index) (upper : index < 135680) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 135424 then
    if cut : index < 135296 then
      exact segment_sound _ 135168 128 Update0264_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 135296 128 Update0264_1_checked index (by omega) (by omega)
  else
    if cut : index < 135552 then
      exact segment_sound _ 135424 128 Update0264_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 135552 128 Update0264_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
