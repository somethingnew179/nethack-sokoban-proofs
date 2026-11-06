import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0577_0_checked : (List.range' 295424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0577_1_checked : (List.range' 295552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0577_2_checked : (List.range' 295680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0577_3_checked : (List.range' 295808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0577_range (index : Nat) (lower : 295424 ≤ index) (upper : index < 295936) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 295680 then
    if cut : index < 295552 then
      exact segment_sound _ 295424 128 Update0577_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 295552 128 Update0577_1_checked index (by omega) (by omega)
  else
    if cut : index < 295808 then
      exact segment_sound _ 295680 128 Update0577_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 295808 128 Update0577_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
