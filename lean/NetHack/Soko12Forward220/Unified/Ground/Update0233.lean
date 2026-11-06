import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0233_0_checked : (List.range' 119296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0233_1_checked : (List.range' 119424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0233_2_checked : (List.range' 119552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0233_3_checked : (List.range' 119680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0233_range (index : Nat) (lower : 119296 ≤ index) (upper : index < 119808) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 119552 then
    if cut : index < 119424 then
      exact segment_sound _ 119296 128 Update0233_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 119424 128 Update0233_1_checked index (by omega) (by omega)
  else
    if cut : index < 119680 then
      exact segment_sound _ 119552 128 Update0233_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 119680 128 Update0233_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
