import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0132_0_checked : (List.range' 67584 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0132_1_checked : (List.range' 67712 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0132_2_checked : (List.range' 67840 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0132_3_checked : (List.range' 67968 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0132_range (index : Nat) (lower : 67584 ≤ index) (upper : index < 68096) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 67840 then
    if cut : index < 67712 then
      exact segment_sound _ 67584 128 Update0132_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 67712 128 Update0132_1_checked index (by omega) (by omega)
  else
    if cut : index < 67968 then
      exact segment_sound _ 67840 128 Update0132_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 67968 128 Update0132_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
