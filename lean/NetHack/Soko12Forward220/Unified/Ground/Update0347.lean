import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0347_0_checked : (List.range' 177664 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0347_1_checked : (List.range' 177792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0347_2_checked : (List.range' 177920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0347_3_checked : (List.range' 178048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0347_range (index : Nat) (lower : 177664 ≤ index) (upper : index < 178176) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 177920 then
    if cut : index < 177792 then
      exact segment_sound _ 177664 128 Update0347_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 177792 128 Update0347_1_checked index (by omega) (by omega)
  else
    if cut : index < 178048 then
      exact segment_sound _ 177920 128 Update0347_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 178048 128 Update0347_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
