import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0190_0_checked : (List.range' 97280 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0190_1_checked : (List.range' 97408 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0190_2_checked : (List.range' 97536 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0190_3_checked : (List.range' 97664 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0190_range (index : Nat) (lower : 97280 ≤ index) (upper : index < 97792) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 97536 then
    if cut : index < 97408 then
      exact segment_sound _ 97280 128 Update0190_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 97408 128 Update0190_1_checked index (by omega) (by omega)
  else
    if cut : index < 97664 then
      exact segment_sound _ 97536 128 Update0190_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 97664 128 Update0190_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
