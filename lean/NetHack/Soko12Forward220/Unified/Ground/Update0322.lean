import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0322_0_checked : (List.range' 164864 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0322_1_checked : (List.range' 164992 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0322_2_checked : (List.range' 165120 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0322_3_checked : (List.range' 165248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0322_range (index : Nat) (lower : 164864 ≤ index) (upper : index < 165376) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 165120 then
    if cut : index < 164992 then
      exact segment_sound _ 164864 128 Update0322_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 164992 128 Update0322_1_checked index (by omega) (by omega)
  else
    if cut : index < 165248 then
      exact segment_sound _ 165120 128 Update0322_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 165248 128 Update0322_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
