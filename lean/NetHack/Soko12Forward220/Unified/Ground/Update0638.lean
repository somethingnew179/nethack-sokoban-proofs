import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0638_0_checked : (List.range' 326656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0638_1_checked : (List.range' 326784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0638_2_checked : (List.range' 326912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0638_3_checked : (List.range' 327040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0638_range (index : Nat) (lower : 326656 ≤ index) (upper : index < 327168) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 326912 then
    if cut : index < 326784 then
      exact segment_sound _ 326656 128 Update0638_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 326784 128 Update0638_1_checked index (by omega) (by omega)
  else
    if cut : index < 327040 then
      exact segment_sound _ 326912 128 Update0638_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 327040 128 Update0638_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
