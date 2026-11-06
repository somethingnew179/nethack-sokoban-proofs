import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0430_0_checked : (List.range' 220160 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0430_1_checked : (List.range' 220288 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0430_2_checked : (List.range' 220416 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0430_3_checked : (List.range' 220544 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0430_range (index : Nat) (lower : 220160 ≤ index) (upper : index < 220672) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 220416 then
    if cut : index < 220288 then
      exact segment_sound _ 220160 128 Update0430_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 220288 128 Update0430_1_checked index (by omega) (by omega)
  else
    if cut : index < 220544 then
      exact segment_sound _ 220416 128 Update0430_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 220544 128 Update0430_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
