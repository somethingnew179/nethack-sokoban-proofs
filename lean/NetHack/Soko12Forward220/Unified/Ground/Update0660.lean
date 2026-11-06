import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0660_0_checked : (List.range' 337920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0660_1_checked : (List.range' 338048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0660_2_checked : (List.range' 338176 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0660_3_checked : (List.range' 338304 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0660_range (index : Nat) (lower : 337920 ≤ index) (upper : index < 338432) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 338176 then
    if cut : index < 338048 then
      exact segment_sound _ 337920 128 Update0660_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 338048 128 Update0660_1_checked index (by omega) (by omega)
  else
    if cut : index < 338304 then
      exact segment_sound _ 338176 128 Update0660_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 338304 128 Update0660_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
