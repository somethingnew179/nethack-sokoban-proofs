import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0217_0_checked : (List.range' 111104 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0217_1_checked : (List.range' 111232 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0217_2_checked : (List.range' 111360 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0217_3_checked : (List.range' 111488 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0217_range (index : Nat) (lower : 111104 ≤ index) (upper : index < 111616) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 111360 then
    if cut : index < 111232 then
      exact segment_sound _ 111104 128 Update0217_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 111232 128 Update0217_1_checked index (by omega) (by omega)
  else
    if cut : index < 111488 then
      exact segment_sound _ 111360 128 Update0217_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 111488 128 Update0217_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
