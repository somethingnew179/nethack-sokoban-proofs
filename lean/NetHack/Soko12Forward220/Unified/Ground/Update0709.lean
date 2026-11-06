import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0709_0_checked : (List.range' 363008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0709_1_checked : (List.range' 363136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0709_2_checked : (List.range' 363264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0709_3_checked : (List.range' 363392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0709_range (index : Nat) (lower : 363008 ≤ index) (upper : index < 363520) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 363264 then
    if cut : index < 363136 then
      exact segment_sound _ 363008 128 Update0709_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 363136 128 Update0709_1_checked index (by omega) (by omega)
  else
    if cut : index < 363392 then
      exact segment_sound _ 363264 128 Update0709_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 363392 128 Update0709_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
