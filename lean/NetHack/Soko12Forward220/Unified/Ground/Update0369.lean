import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0369_0_checked : (List.range' 188928 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0369_1_checked : (List.range' 189056 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0369_2_checked : (List.range' 189184 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0369_3_checked : (List.range' 189312 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0369_range (index : Nat) (lower : 188928 ≤ index) (upper : index < 189440) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 189184 then
    if cut : index < 189056 then
      exact segment_sound _ 188928 128 Update0369_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 189056 128 Update0369_1_checked index (by omega) (by omega)
  else
    if cut : index < 189312 then
      exact segment_sound _ 189184 128 Update0369_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 189312 128 Update0369_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
