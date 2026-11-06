import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0594_0_checked : (List.range' 304128 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0594_1_checked : (List.range' 304256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0594_2_checked : (List.range' 304384 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0594_3_checked : (List.range' 304512 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0594_range (index : Nat) (lower : 304128 ≤ index) (upper : index < 304640) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 304384 then
    if cut : index < 304256 then
      exact segment_sound _ 304128 128 Update0594_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 304256 128 Update0594_1_checked index (by omega) (by omega)
  else
    if cut : index < 304512 then
      exact segment_sound _ 304384 128 Update0594_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 304512 128 Update0594_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
