import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0729_0_checked : (List.range' 373248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0729_1_checked : (List.range' 373376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0729_2_checked : (List.range' 373504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0729_3_checked : (List.range' 373632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0729_range (index : Nat) (lower : 373248 ≤ index) (upper : index < 373760) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 373504 then
    if cut : index < 373376 then
      exact segment_sound _ 373248 128 Update0729_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 373376 128 Update0729_1_checked index (by omega) (by omega)
  else
    if cut : index < 373632 then
      exact segment_sound _ 373504 128 Update0729_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 373632 128 Update0729_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
