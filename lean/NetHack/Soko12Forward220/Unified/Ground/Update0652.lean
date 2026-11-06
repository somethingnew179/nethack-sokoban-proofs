import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0652_0_checked : (List.range' 333824 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0652_1_checked : (List.range' 333952 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0652_2_checked : (List.range' 334080 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0652_3_checked : (List.range' 334208 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0652_range (index : Nat) (lower : 333824 ≤ index) (upper : index < 334336) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 334080 then
    if cut : index < 333952 then
      exact segment_sound _ 333824 128 Update0652_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 333952 128 Update0652_1_checked index (by omega) (by omega)
  else
    if cut : index < 334208 then
      exact segment_sound _ 334080 128 Update0652_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 334208 128 Update0652_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
