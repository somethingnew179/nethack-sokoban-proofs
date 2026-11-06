import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0421_0_checked : (List.range' 215552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0421_1_checked : (List.range' 215680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0421_2_checked : (List.range' 215808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0421_3_checked : (List.range' 215936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0421_range (index : Nat) (lower : 215552 ≤ index) (upper : index < 216064) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 215808 then
    if cut : index < 215680 then
      exact segment_sound _ 215552 128 Update0421_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 215680 128 Update0421_1_checked index (by omega) (by omega)
  else
    if cut : index < 215936 then
      exact segment_sound _ 215808 128 Update0421_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 215936 128 Update0421_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
