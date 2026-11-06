import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0027_0_checked : (List.range' 13824 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0027_1_checked : (List.range' 13952 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0027_2_checked : (List.range' 14080 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0027_3_checked : (List.range' 14208 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0027_range (index : Nat) (lower : 13824 ≤ index) (upper : index < 14336) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 14080 then
    if cut : index < 13952 then
      exact segment_sound _ 13824 128 Update0027_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 13952 128 Update0027_1_checked index (by omega) (by omega)
  else
    if cut : index < 14208 then
      exact segment_sound _ 14080 128 Update0027_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 14208 128 Update0027_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
