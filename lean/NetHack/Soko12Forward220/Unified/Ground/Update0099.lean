import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0099_0_checked : (List.range' 50688 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0099_1_checked : (List.range' 50816 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0099_2_checked : (List.range' 50944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0099_3_checked : (List.range' 51072 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0099_range (index : Nat) (lower : 50688 ≤ index) (upper : index < 51200) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 50944 then
    if cut : index < 50816 then
      exact segment_sound _ 50688 128 Update0099_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 50816 128 Update0099_1_checked index (by omega) (by omega)
  else
    if cut : index < 51072 then
      exact segment_sound _ 50944 128 Update0099_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 51072 128 Update0099_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
