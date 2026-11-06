import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0613_0_checked : (List.range' 313856 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0613_1_checked : (List.range' 313984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0613_2_checked : (List.range' 314112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0613_3_checked : (List.range' 314240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0613_range (index : Nat) (lower : 313856 ≤ index) (upper : index < 314368) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 314112 then
    if cut : index < 313984 then
      exact segment_sound _ 313856 128 Update0613_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 313984 128 Update0613_1_checked index (by omega) (by omega)
  else
    if cut : index < 314240 then
      exact segment_sound _ 314112 128 Update0613_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 314240 128 Update0613_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
