import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0201_0_checked : (List.range' 102912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0201_1_checked : (List.range' 103040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0201_2_checked : (List.range' 103168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0201_3_checked : (List.range' 103296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0201_range (index : Nat) (lower : 102912 ≤ index) (upper : index < 103424) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 103168 then
    if cut : index < 103040 then
      exact segment_sound _ 102912 128 Update0201_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 103040 128 Update0201_1_checked index (by omega) (by omega)
  else
    if cut : index < 103296 then
      exact segment_sound _ 103168 128 Update0201_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 103296 128 Update0201_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
