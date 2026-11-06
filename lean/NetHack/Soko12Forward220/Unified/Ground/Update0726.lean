import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0726_0_checked : (List.range' 371712 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0726_1_checked : (List.range' 371840 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0726_2_checked : (List.range' 371968 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0726_3_checked : (List.range' 372096 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0726_range (index : Nat) (lower : 371712 ≤ index) (upper : index < 372224) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 371968 then
    if cut : index < 371840 then
      exact segment_sound _ 371712 128 Update0726_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 371840 128 Update0726_1_checked index (by omega) (by omega)
  else
    if cut : index < 372096 then
      exact segment_sound _ 371968 128 Update0726_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 372096 128 Update0726_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
