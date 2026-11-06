import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0279_0_checked : (List.range' 142848 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0279_1_checked : (List.range' 142976 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0279_2_checked : (List.range' 143104 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0279_3_checked : (List.range' 143232 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0279_range (index : Nat) (lower : 142848 ≤ index) (upper : index < 143360) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 143104 then
    if cut : index < 142976 then
      exact segment_sound _ 142848 128 Update0279_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 142976 128 Update0279_1_checked index (by omega) (by omega)
  else
    if cut : index < 143232 then
      exact segment_sound _ 143104 128 Update0279_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 143232 128 Update0279_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
