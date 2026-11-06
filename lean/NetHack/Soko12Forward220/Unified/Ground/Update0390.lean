import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0390_0_checked : (List.range' 199680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0390_1_checked : (List.range' 199808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0390_2_checked : (List.range' 199936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0390_3_checked : (List.range' 200064 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0390_range (index : Nat) (lower : 199680 ≤ index) (upper : index < 200192) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 199936 then
    if cut : index < 199808 then
      exact segment_sound _ 199680 128 Update0390_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 199808 128 Update0390_1_checked index (by omega) (by omega)
  else
    if cut : index < 200064 then
      exact segment_sound _ 199936 128 Update0390_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 200064 128 Update0390_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
