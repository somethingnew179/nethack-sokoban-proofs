import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0734_0_checked : (List.range' 375808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0734_1_checked : (List.range' 375936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0734_2_checked : (List.range' 376064 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0734_3_checked : (List.range' 376192 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0734_range (index : Nat) (lower : 375808 ≤ index) (upper : index < 376320) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 376064 then
    if cut : index < 375936 then
      exact segment_sound _ 375808 128 Update0734_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 375936 128 Update0734_1_checked index (by omega) (by omega)
  else
    if cut : index < 376192 then
      exact segment_sound _ 376064 128 Update0734_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 376192 128 Update0734_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
