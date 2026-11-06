import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0518_0_checked : (List.range' 265216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0518_1_checked : (List.range' 265344 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0518_2_checked : (List.range' 265472 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0518_3_checked : (List.range' 265600 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0518_range (index : Nat) (lower : 265216 ≤ index) (upper : index < 265728) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 265472 then
    if cut : index < 265344 then
      exact segment_sound _ 265216 128 Update0518_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 265344 128 Update0518_1_checked index (by omega) (by omega)
  else
    if cut : index < 265600 then
      exact segment_sound _ 265472 128 Update0518_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 265600 128 Update0518_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
