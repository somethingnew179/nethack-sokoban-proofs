import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0560_0_checked : (List.range' 286720 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0560_1_checked : (List.range' 286848 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0560_2_checked : (List.range' 286976 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0560_3_checked : (List.range' 287104 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0560_range (index : Nat) (lower : 286720 ≤ index) (upper : index < 287232) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 286976 then
    if cut : index < 286848 then
      exact segment_sound _ 286720 128 Update0560_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 286848 128 Update0560_1_checked index (by omega) (by omega)
  else
    if cut : index < 287104 then
      exact segment_sound _ 286976 128 Update0560_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 287104 128 Update0560_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
