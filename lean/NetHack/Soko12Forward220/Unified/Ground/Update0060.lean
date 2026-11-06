import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0060_0_checked : (List.range' 30720 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0060_1_checked : (List.range' 30848 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0060_2_checked : (List.range' 30976 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0060_3_checked : (List.range' 31104 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0060_range (index : Nat) (lower : 30720 ≤ index) (upper : index < 31232) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 30976 then
    if cut : index < 30848 then
      exact segment_sound _ 30720 128 Update0060_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 30848 128 Update0060_1_checked index (by omega) (by omega)
  else
    if cut : index < 31104 then
      exact segment_sound _ 30976 128 Update0060_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 31104 128 Update0060_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
