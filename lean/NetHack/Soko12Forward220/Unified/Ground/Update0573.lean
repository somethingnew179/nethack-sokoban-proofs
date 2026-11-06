import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0573_0_checked : (List.range' 293376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0573_1_checked : (List.range' 293504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0573_2_checked : (List.range' 293632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0573_3_checked : (List.range' 293760 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0573_range (index : Nat) (lower : 293376 ≤ index) (upper : index < 293888) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 293632 then
    if cut : index < 293504 then
      exact segment_sound _ 293376 128 Update0573_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 293504 128 Update0573_1_checked index (by omega) (by omega)
  else
    if cut : index < 293760 then
      exact segment_sound _ 293632 128 Update0573_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 293760 128 Update0573_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
