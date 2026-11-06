import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0462_0_checked : (List.range' 236544 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0462_1_checked : (List.range' 236672 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0462_2_checked : (List.range' 236800 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0462_3_checked : (List.range' 236928 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0462_range (index : Nat) (lower : 236544 ≤ index) (upper : index < 237056) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 236800 then
    if cut : index < 236672 then
      exact segment_sound _ 236544 128 Update0462_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 236672 128 Update0462_1_checked index (by omega) (by omega)
  else
    if cut : index < 236928 then
      exact segment_sound _ 236800 128 Update0462_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 236928 128 Update0462_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
