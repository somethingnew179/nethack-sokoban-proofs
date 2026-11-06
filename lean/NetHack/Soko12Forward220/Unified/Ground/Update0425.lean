import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0425_0_checked : (List.range' 217600 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0425_1_checked : (List.range' 217728 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0425_2_checked : (List.range' 217856 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0425_3_checked : (List.range' 217984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0425_range (index : Nat) (lower : 217600 ≤ index) (upper : index < 218112) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 217856 then
    if cut : index < 217728 then
      exact segment_sound _ 217600 128 Update0425_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 217728 128 Update0425_1_checked index (by omega) (by omega)
  else
    if cut : index < 217984 then
      exact segment_sound _ 217856 128 Update0425_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 217984 128 Update0425_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
