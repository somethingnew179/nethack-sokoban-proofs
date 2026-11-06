import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0063_0_checked : (List.range' 32256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0063_1_checked : (List.range' 32384 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0063_2_checked : (List.range' 32512 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0063_3_checked : (List.range' 32640 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0063_range (index : Nat) (lower : 32256 ≤ index) (upper : index < 32768) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 32512 then
    if cut : index < 32384 then
      exact segment_sound _ 32256 128 Update0063_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 32384 128 Update0063_1_checked index (by omega) (by omega)
  else
    if cut : index < 32640 then
      exact segment_sound _ 32512 128 Update0063_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 32640 128 Update0063_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
