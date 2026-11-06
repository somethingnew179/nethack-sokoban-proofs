import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0543_0_checked : (List.range' 278016 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0543_1_checked : (List.range' 278144 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0543_2_checked : (List.range' 278272 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0543_3_checked : (List.range' 278400 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0543_range (index : Nat) (lower : 278016 ≤ index) (upper : index < 278528) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 278272 then
    if cut : index < 278144 then
      exact segment_sound _ 278016 128 Update0543_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 278144 128 Update0543_1_checked index (by omega) (by omega)
  else
    if cut : index < 278400 then
      exact segment_sound _ 278272 128 Update0543_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 278400 128 Update0543_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
