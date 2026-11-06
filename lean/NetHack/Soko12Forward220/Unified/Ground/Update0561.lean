import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0561_0_checked : (List.range' 287232 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0561_1_checked : (List.range' 287360 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0561_2_checked : (List.range' 287488 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0561_3_checked : (List.range' 287616 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0561_range (index : Nat) (lower : 287232 ≤ index) (upper : index < 287744) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 287488 then
    if cut : index < 287360 then
      exact segment_sound _ 287232 128 Update0561_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 287360 128 Update0561_1_checked index (by omega) (by omega)
  else
    if cut : index < 287616 then
      exact segment_sound _ 287488 128 Update0561_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 287616 128 Update0561_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
