import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0704_0_checked : (List.range' 360448 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0704_1_checked : (List.range' 360576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0704_2_checked : (List.range' 360704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0704_3_checked : (List.range' 360832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0704_range (index : Nat) (lower : 360448 ≤ index) (upper : index < 360960) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 360704 then
    if cut : index < 360576 then
      exact segment_sound _ 360448 128 Update0704_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 360576 128 Update0704_1_checked index (by omega) (by omega)
  else
    if cut : index < 360832 then
      exact segment_sound _ 360704 128 Update0704_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 360832 128 Update0704_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
