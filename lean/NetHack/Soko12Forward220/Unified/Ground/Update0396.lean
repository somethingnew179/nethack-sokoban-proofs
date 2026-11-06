import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0396_0_checked : (List.range' 202752 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0396_1_checked : (List.range' 202880 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0396_2_checked : (List.range' 203008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0396_3_checked : (List.range' 203136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0396_range (index : Nat) (lower : 202752 ≤ index) (upper : index < 203264) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 203008 then
    if cut : index < 202880 then
      exact segment_sound _ 202752 128 Update0396_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 202880 128 Update0396_1_checked index (by omega) (by omega)
  else
    if cut : index < 203136 then
      exact segment_sound _ 203008 128 Update0396_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 203136 128 Update0396_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
