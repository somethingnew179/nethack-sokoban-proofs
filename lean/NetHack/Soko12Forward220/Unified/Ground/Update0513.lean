import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0513_0_checked : (List.range' 262656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0513_1_checked : (List.range' 262784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0513_2_checked : (List.range' 262912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0513_3_checked : (List.range' 263040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0513_range (index : Nat) (lower : 262656 ≤ index) (upper : index < 263168) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 262912 then
    if cut : index < 262784 then
      exact segment_sound _ 262656 128 Update0513_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 262784 128 Update0513_1_checked index (by omega) (by omega)
  else
    if cut : index < 263040 then
      exact segment_sound _ 262912 128 Update0513_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 263040 128 Update0513_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
