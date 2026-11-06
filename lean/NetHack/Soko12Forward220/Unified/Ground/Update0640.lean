import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0640_0_checked : (List.range' 327680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0640_1_checked : (List.range' 327808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0640_2_checked : (List.range' 327936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0640_3_checked : (List.range' 328064 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0640_range (index : Nat) (lower : 327680 ≤ index) (upper : index < 328192) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 327936 then
    if cut : index < 327808 then
      exact segment_sound _ 327680 128 Update0640_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 327808 128 Update0640_1_checked index (by omega) (by omega)
  else
    if cut : index < 328064 then
      exact segment_sound _ 327936 128 Update0640_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 328064 128 Update0640_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
