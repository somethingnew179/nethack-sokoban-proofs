import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0437_0_checked : (List.range' 223744 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0437_1_checked : (List.range' 223872 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0437_2_checked : (List.range' 224000 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0437_3_checked : (List.range' 224128 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0437_range (index : Nat) (lower : 223744 ≤ index) (upper : index < 224256) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 224000 then
    if cut : index < 223872 then
      exact segment_sound _ 223744 128 Update0437_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 223872 128 Update0437_1_checked index (by omega) (by omega)
  else
    if cut : index < 224128 then
      exact segment_sound _ 224000 128 Update0437_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 224128 128 Update0437_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
