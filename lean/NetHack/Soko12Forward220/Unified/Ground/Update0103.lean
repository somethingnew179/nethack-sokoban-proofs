import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0103_0_checked : (List.range' 52736 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0103_1_checked : (List.range' 52864 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0103_2_checked : (List.range' 52992 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0103_3_checked : (List.range' 53120 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0103_range (index : Nat) (lower : 52736 ≤ index) (upper : index < 53248) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 52992 then
    if cut : index < 52864 then
      exact segment_sound _ 52736 128 Update0103_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 52864 128 Update0103_1_checked index (by omega) (by omega)
  else
    if cut : index < 53120 then
      exact segment_sound _ 52992 128 Update0103_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 53120 128 Update0103_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
