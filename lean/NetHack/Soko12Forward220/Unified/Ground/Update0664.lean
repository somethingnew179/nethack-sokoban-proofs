import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0664_0_checked : (List.range' 339968 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0664_1_checked : (List.range' 340096 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0664_2_checked : (List.range' 340224 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0664_3_checked : (List.range' 340352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0664_range (index : Nat) (lower : 339968 ≤ index) (upper : index < 340480) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 340224 then
    if cut : index < 340096 then
      exact segment_sound _ 339968 128 Update0664_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 340096 128 Update0664_1_checked index (by omega) (by omega)
  else
    if cut : index < 340352 then
      exact segment_sound _ 340224 128 Update0664_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 340352 128 Update0664_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
