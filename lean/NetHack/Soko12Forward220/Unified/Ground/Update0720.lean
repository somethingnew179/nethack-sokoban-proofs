import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0720_0_checked : (List.range' 368640 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0720_1_checked : (List.range' 368768 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0720_2_checked : (List.range' 368896 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0720_3_checked : (List.range' 369024 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0720_range (index : Nat) (lower : 368640 ≤ index) (upper : index < 369152) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 368896 then
    if cut : index < 368768 then
      exact segment_sound _ 368640 128 Update0720_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 368768 128 Update0720_1_checked index (by omega) (by omega)
  else
    if cut : index < 369024 then
      exact segment_sound _ 368896 128 Update0720_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 369024 128 Update0720_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
