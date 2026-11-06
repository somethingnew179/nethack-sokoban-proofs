import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0335_0_checked : (List.range' 171520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0335_1_checked : (List.range' 171648 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0335_2_checked : (List.range' 171776 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0335_3_checked : (List.range' 171904 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0335_range (index : Nat) (lower : 171520 ≤ index) (upper : index < 172032) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 171776 then
    if cut : index < 171648 then
      exact segment_sound _ 171520 128 Update0335_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 171648 128 Update0335_1_checked index (by omega) (by omega)
  else
    if cut : index < 171904 then
      exact segment_sound _ 171776 128 Update0335_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 171904 128 Update0335_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
