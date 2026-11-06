import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0544_0_checked : (List.range' 278528 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0544_1_checked : (List.range' 278656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0544_2_checked : (List.range' 278784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0544_3_checked : (List.range' 278912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0544_range (index : Nat) (lower : 278528 ≤ index) (upper : index < 279040) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 278784 then
    if cut : index < 278656 then
      exact segment_sound _ 278528 128 Update0544_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 278656 128 Update0544_1_checked index (by omega) (by omega)
  else
    if cut : index < 278912 then
      exact segment_sound _ 278784 128 Update0544_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 278912 128 Update0544_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
