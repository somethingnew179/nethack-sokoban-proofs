import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0422_0_checked : (List.range' 216064 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0422_1_checked : (List.range' 216192 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0422_2_checked : (List.range' 216320 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0422_3_checked : (List.range' 216448 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0422_range (index : Nat) (lower : 216064 ≤ index) (upper : index < 216576) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 216320 then
    if cut : index < 216192 then
      exact segment_sound _ 216064 128 Update0422_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 216192 128 Update0422_1_checked index (by omega) (by omega)
  else
    if cut : index < 216448 then
      exact segment_sound _ 216320 128 Update0422_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 216448 128 Update0422_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
