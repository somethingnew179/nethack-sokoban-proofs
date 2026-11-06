import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0376_0_checked : (List.range' 192512 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0376_1_checked : (List.range' 192640 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0376_2_checked : (List.range' 192768 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0376_3_checked : (List.range' 192896 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0376_range (index : Nat) (lower : 192512 ≤ index) (upper : index < 193024) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 192768 then
    if cut : index < 192640 then
      exact segment_sound _ 192512 128 Update0376_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 192640 128 Update0376_1_checked index (by omega) (by omega)
  else
    if cut : index < 192896 then
      exact segment_sound _ 192768 128 Update0376_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 192896 128 Update0376_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
