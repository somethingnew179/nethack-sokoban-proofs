import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0687_0_checked : (List.range' 351744 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0687_1_checked : (List.range' 351872 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0687_2_checked : (List.range' 352000 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0687_3_checked : (List.range' 352128 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0687_range (index : Nat) (lower : 351744 ≤ index) (upper : index < 352256) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 352000 then
    if cut : index < 351872 then
      exact segment_sound _ 351744 128 Update0687_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 351872 128 Update0687_1_checked index (by omega) (by omega)
  else
    if cut : index < 352128 then
      exact segment_sound _ 352000 128 Update0687_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 352128 128 Update0687_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
