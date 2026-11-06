import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0289_0_checked : (List.range' 147968 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0289_1_checked : (List.range' 148096 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0289_2_checked : (List.range' 148224 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0289_3_checked : (List.range' 148352 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0289_range (index : Nat) (lower : 147968 ≤ index) (upper : index < 148480) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 148224 then
    if cut : index < 148096 then
      exact segment_sound _ 147968 128 Update0289_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 148096 128 Update0289_1_checked index (by omega) (by omega)
  else
    if cut : index < 148352 then
      exact segment_sound _ 148224 128 Update0289_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 148352 128 Update0289_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
