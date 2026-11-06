import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0719_0_checked : (List.range' 368128 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0719_1_checked : (List.range' 368256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0719_2_checked : (List.range' 368384 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0719_3_checked : (List.range' 368512 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0719_range (index : Nat) (lower : 368128 ≤ index) (upper : index < 368640) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 368384 then
    if cut : index < 368256 then
      exact segment_sound _ 368128 128 Update0719_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 368256 128 Update0719_1_checked index (by omega) (by omega)
  else
    if cut : index < 368512 then
      exact segment_sound _ 368384 128 Update0719_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 368512 128 Update0719_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
