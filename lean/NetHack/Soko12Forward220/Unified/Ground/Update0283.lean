import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0283_0_checked : (List.range' 144896 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0283_1_checked : (List.range' 145024 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0283_2_checked : (List.range' 145152 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0283_3_checked : (List.range' 145280 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0283_range (index : Nat) (lower : 144896 ≤ index) (upper : index < 145408) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 145152 then
    if cut : index < 145024 then
      exact segment_sound _ 144896 128 Update0283_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 145024 128 Update0283_1_checked index (by omega) (by omega)
  else
    if cut : index < 145280 then
      exact segment_sound _ 145152 128 Update0283_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 145280 128 Update0283_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
