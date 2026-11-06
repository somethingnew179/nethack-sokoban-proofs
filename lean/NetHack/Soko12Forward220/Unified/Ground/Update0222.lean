import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0222_0_checked : (List.range' 113664 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0222_1_checked : (List.range' 113792 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0222_2_checked : (List.range' 113920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0222_3_checked : (List.range' 114048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0222_range (index : Nat) (lower : 113664 ≤ index) (upper : index < 114176) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 113920 then
    if cut : index < 113792 then
      exact segment_sound _ 113664 128 Update0222_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 113792 128 Update0222_1_checked index (by omega) (by omega)
  else
    if cut : index < 114048 then
      exact segment_sound _ 113920 128 Update0222_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 114048 128 Update0222_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
