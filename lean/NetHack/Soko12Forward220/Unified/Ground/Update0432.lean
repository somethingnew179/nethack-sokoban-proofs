import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0432_0_checked : (List.range' 221184 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0432_1_checked : (List.range' 221312 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0432_2_checked : (List.range' 221440 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0432_3_checked : (List.range' 221568 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0432_range (index : Nat) (lower : 221184 ≤ index) (upper : index < 221696) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 221440 then
    if cut : index < 221312 then
      exact segment_sound _ 221184 128 Update0432_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 221312 128 Update0432_1_checked index (by omega) (by omega)
  else
    if cut : index < 221568 then
      exact segment_sound _ 221440 128 Update0432_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 221568 128 Update0432_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
