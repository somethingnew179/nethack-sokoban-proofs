import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0693_0_checked : (List.range' 354816 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0693_1_checked : (List.range' 354944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0693_2_checked : (List.range' 355072 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0693_3_checked : (List.range' 355200 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0693_range (index : Nat) (lower : 354816 ≤ index) (upper : index < 355328) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 355072 then
    if cut : index < 354944 then
      exact segment_sound _ 354816 128 Update0693_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 354944 128 Update0693_1_checked index (by omega) (by omega)
  else
    if cut : index < 355200 then
      exact segment_sound _ 355072 128 Update0693_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 355200 128 Update0693_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
