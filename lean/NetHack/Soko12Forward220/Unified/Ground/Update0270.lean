import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0270_0_checked : (List.range' 138240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0270_1_checked : (List.range' 138368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0270_2_checked : (List.range' 138496 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0270_3_checked : (List.range' 138624 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0270_range (index : Nat) (lower : 138240 ≤ index) (upper : index < 138752) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 138496 then
    if cut : index < 138368 then
      exact segment_sound _ 138240 128 Update0270_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 138368 128 Update0270_1_checked index (by omega) (by omega)
  else
    if cut : index < 138624 then
      exact segment_sound _ 138496 128 Update0270_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 138624 128 Update0270_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
