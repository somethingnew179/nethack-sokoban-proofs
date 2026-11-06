import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0439_0_checked : (List.range' 224768 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0439_1_checked : (List.range' 224896 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0439_2_checked : (List.range' 225024 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0439_3_checked : (List.range' 225152 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0439_range (index : Nat) (lower : 224768 ≤ index) (upper : index < 225280) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 225024 then
    if cut : index < 224896 then
      exact segment_sound _ 224768 128 Update0439_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 224896 128 Update0439_1_checked index (by omega) (by omega)
  else
    if cut : index < 225152 then
      exact segment_sound _ 225024 128 Update0439_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 225152 128 Update0439_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
