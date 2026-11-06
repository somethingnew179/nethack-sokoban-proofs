import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0666_0_checked : (List.range' 340992 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0666_1_checked : (List.range' 341120 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0666_2_checked : (List.range' 341248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0666_3_checked : (List.range' 341376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0666_range (index : Nat) (lower : 340992 ≤ index) (upper : index < 341504) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 341248 then
    if cut : index < 341120 then
      exact segment_sound _ 340992 128 Update0666_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 341120 128 Update0666_1_checked index (by omega) (by omega)
  else
    if cut : index < 341376 then
      exact segment_sound _ 341248 128 Update0666_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 341376 128 Update0666_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
