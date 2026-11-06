import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0428_0_checked : (List.range' 219136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0428_1_checked : (List.range' 219264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0428_2_checked : (List.range' 219392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0428_3_checked : (List.range' 219520 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0428_range (index : Nat) (lower : 219136 ≤ index) (upper : index < 219648) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 219392 then
    if cut : index < 219264 then
      exact segment_sound _ 219136 128 Update0428_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 219264 128 Update0428_1_checked index (by omega) (by omega)
  else
    if cut : index < 219520 then
      exact segment_sound _ 219392 128 Update0428_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 219520 128 Update0428_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
