import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0580_0_checked : (List.range' 296960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0580_1_checked : (List.range' 297088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0580_2_checked : (List.range' 297216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0580_3_checked : (List.range' 297344 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0580_range (index : Nat) (lower : 296960 ≤ index) (upper : index < 297472) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 297216 then
    if cut : index < 297088 then
      exact segment_sound _ 296960 128 Update0580_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 297088 128 Update0580_1_checked index (by omega) (by omega)
  else
    if cut : index < 297344 then
      exact segment_sound _ 297216 128 Update0580_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 297344 128 Update0580_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
