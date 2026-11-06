import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0546_0_checked : (List.range' 279552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0546_1_checked : (List.range' 279680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0546_2_checked : (List.range' 279808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0546_3_checked : (List.range' 279936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0546_range (index : Nat) (lower : 279552 ≤ index) (upper : index < 280064) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 279808 then
    if cut : index < 279680 then
      exact segment_sound _ 279552 128 Update0546_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 279680 128 Update0546_1_checked index (by omega) (by omega)
  else
    if cut : index < 279936 then
      exact segment_sound _ 279808 128 Update0546_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 279936 128 Update0546_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
