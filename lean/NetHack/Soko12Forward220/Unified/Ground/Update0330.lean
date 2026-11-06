import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0330_0_checked : (List.range' 168960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0330_1_checked : (List.range' 169088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0330_2_checked : (List.range' 169216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0330_3_checked : (List.range' 169344 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0330_range (index : Nat) (lower : 168960 ≤ index) (upper : index < 169472) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 169216 then
    if cut : index < 169088 then
      exact segment_sound _ 168960 128 Update0330_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 169088 128 Update0330_1_checked index (by omega) (by omega)
  else
    if cut : index < 169344 then
      exact segment_sound _ 169216 128 Update0330_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 169344 128 Update0330_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
