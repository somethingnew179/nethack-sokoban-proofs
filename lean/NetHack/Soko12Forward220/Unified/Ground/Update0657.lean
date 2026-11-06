import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0657_0_checked : (List.range' 336384 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0657_1_checked : (List.range' 336512 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0657_2_checked : (List.range' 336640 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0657_3_checked : (List.range' 336768 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0657_range (index : Nat) (lower : 336384 ≤ index) (upper : index < 336896) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 336640 then
    if cut : index < 336512 then
      exact segment_sound _ 336384 128 Update0657_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 336512 128 Update0657_1_checked index (by omega) (by omega)
  else
    if cut : index < 336768 then
      exact segment_sound _ 336640 128 Update0657_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 336768 128 Update0657_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
