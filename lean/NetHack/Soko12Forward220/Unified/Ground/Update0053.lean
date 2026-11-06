import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0053_0_checked : (List.range' 27136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0053_1_checked : (List.range' 27264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0053_2_checked : (List.range' 27392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0053_3_checked : (List.range' 27520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0053_range (index : Nat) (lower : 27136 ≤ index) (upper : index < 27648) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 27392 then
    if cut : index < 27264 then
      exact segment_sound _ 27136 128 Update0053_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 27264 128 Update0053_1_checked index (by omega) (by omega)
  else
    if cut : index < 27520 then
      exact segment_sound _ 27392 128 Update0053_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 27520 128 Update0053_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
