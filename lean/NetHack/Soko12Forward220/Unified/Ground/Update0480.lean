import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0480_0_checked : (List.range' 245760 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0480_1_checked : (List.range' 245888 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0480_2_checked : (List.range' 246016 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0480_3_checked : (List.range' 246144 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0480_range (index : Nat) (lower : 245760 ≤ index) (upper : index < 246272) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 246016 then
    if cut : index < 245888 then
      exact segment_sound _ 245760 128 Update0480_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 245888 128 Update0480_1_checked index (by omega) (by omega)
  else
    if cut : index < 246144 then
      exact segment_sound _ 246016 128 Update0480_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 246144 128 Update0480_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
