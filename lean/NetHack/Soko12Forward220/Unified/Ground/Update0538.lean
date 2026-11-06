import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0538_0_checked : (List.range' 275456 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0538_1_checked : (List.range' 275584 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0538_2_checked : (List.range' 275712 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0538_3_checked : (List.range' 275840 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0538_range (index : Nat) (lower : 275456 ≤ index) (upper : index < 275968) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 275712 then
    if cut : index < 275584 then
      exact segment_sound _ 275456 128 Update0538_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 275584 128 Update0538_1_checked index (by omega) (by omega)
  else
    if cut : index < 275840 then
      exact segment_sound _ 275712 128 Update0538_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 275840 128 Update0538_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
