import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0389_0_checked : (List.range' 199168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0389_1_checked : (List.range' 199296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0389_2_checked : (List.range' 199424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0389_3_checked : (List.range' 199552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0389_range (index : Nat) (lower : 199168 ≤ index) (upper : index < 199680) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 199424 then
    if cut : index < 199296 then
      exact segment_sound _ 199168 128 Update0389_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 199296 128 Update0389_1_checked index (by omega) (by omega)
  else
    if cut : index < 199552 then
      exact segment_sound _ 199424 128 Update0389_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 199552 128 Update0389_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
