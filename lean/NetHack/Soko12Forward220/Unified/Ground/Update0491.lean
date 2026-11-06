import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0491_0_checked : (List.range' 251392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0491_1_checked : (List.range' 251520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0491_2_checked : (List.range' 251648 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0491_3_checked : (List.range' 251776 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0491_range (index : Nat) (lower : 251392 ≤ index) (upper : index < 251904) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 251648 then
    if cut : index < 251520 then
      exact segment_sound _ 251392 128 Update0491_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 251520 128 Update0491_1_checked index (by omega) (by omega)
  else
    if cut : index < 251776 then
      exact segment_sound _ 251648 128 Update0491_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 251776 128 Update0491_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
