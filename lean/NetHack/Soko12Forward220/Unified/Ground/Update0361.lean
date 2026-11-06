import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0361_0_checked : (List.range' 184832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0361_1_checked : (List.range' 184960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0361_2_checked : (List.range' 185088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0361_3_checked : (List.range' 185216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0361_range (index : Nat) (lower : 184832 ≤ index) (upper : index < 185344) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 185088 then
    if cut : index < 184960 then
      exact segment_sound _ 184832 128 Update0361_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 184960 128 Update0361_1_checked index (by omega) (by omega)
  else
    if cut : index < 185216 then
      exact segment_sound _ 185088 128 Update0361_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 185216 128 Update0361_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
