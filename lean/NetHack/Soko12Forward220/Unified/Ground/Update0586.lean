import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0586_0_checked : (List.range' 300032 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0586_1_checked : (List.range' 300160 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0586_2_checked : (List.range' 300288 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0586_3_checked : (List.range' 300416 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0586_range (index : Nat) (lower : 300032 ≤ index) (upper : index < 300544) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 300288 then
    if cut : index < 300160 then
      exact segment_sound _ 300032 128 Update0586_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 300160 128 Update0586_1_checked index (by omega) (by omega)
  else
    if cut : index < 300416 then
      exact segment_sound _ 300288 128 Update0586_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 300416 128 Update0586_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
