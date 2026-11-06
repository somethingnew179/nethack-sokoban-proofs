import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0631_0_checked : (List.range' 323072 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0631_1_checked : (List.range' 323200 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0631_2_checked : (List.range' 323328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0631_3_checked : (List.range' 323456 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0631_range (index : Nat) (lower : 323072 ≤ index) (upper : index < 323584) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 323328 then
    if cut : index < 323200 then
      exact segment_sound _ 323072 128 Update0631_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 323200 128 Update0631_1_checked index (by omega) (by omega)
  else
    if cut : index < 323456 then
      exact segment_sound _ 323328 128 Update0631_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 323456 128 Update0631_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
