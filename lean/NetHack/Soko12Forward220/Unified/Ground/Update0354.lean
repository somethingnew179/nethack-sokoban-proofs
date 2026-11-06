import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0354_0_checked : (List.range' 181248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0354_1_checked : (List.range' 181376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0354_2_checked : (List.range' 181504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0354_3_checked : (List.range' 181632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0354_range (index : Nat) (lower : 181248 ≤ index) (upper : index < 181760) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 181504 then
    if cut : index < 181376 then
      exact segment_sound _ 181248 128 Update0354_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 181376 128 Update0354_1_checked index (by omega) (by omega)
  else
    if cut : index < 181632 then
      exact segment_sound _ 181504 128 Update0354_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 181632 128 Update0354_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
