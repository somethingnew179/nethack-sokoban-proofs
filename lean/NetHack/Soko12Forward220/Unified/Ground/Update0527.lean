import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0527_0_checked : (List.range' 269824 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0527_1_checked : (List.range' 269952 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0527_2_checked : (List.range' 270080 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0527_3_checked : (List.range' 270208 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0527_range (index : Nat) (lower : 269824 ≤ index) (upper : index < 270336) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 270080 then
    if cut : index < 269952 then
      exact segment_sound _ 269824 128 Update0527_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 269952 128 Update0527_1_checked index (by omega) (by omega)
  else
    if cut : index < 270208 then
      exact segment_sound _ 270080 128 Update0527_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 270208 128 Update0527_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
