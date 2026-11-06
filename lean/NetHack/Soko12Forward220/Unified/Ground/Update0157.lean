import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0157_0_checked : (List.range' 80384 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0157_1_checked : (List.range' 80512 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0157_2_checked : (List.range' 80640 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0157_3_checked : (List.range' 80768 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0157_range (index : Nat) (lower : 80384 ≤ index) (upper : index < 80896) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 80640 then
    if cut : index < 80512 then
      exact segment_sound _ 80384 128 Update0157_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 80512 128 Update0157_1_checked index (by omega) (by omega)
  else
    if cut : index < 80768 then
      exact segment_sound _ 80640 128 Update0157_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 80768 128 Update0157_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
