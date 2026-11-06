import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0700_0_checked : (List.range' 358400 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0700_1_checked : (List.range' 358528 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0700_2_checked : (List.range' 358656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0700_3_checked : (List.range' 358784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0700_range (index : Nat) (lower : 358400 ≤ index) (upper : index < 358912) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 358656 then
    if cut : index < 358528 then
      exact segment_sound _ 358400 128 Update0700_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 358528 128 Update0700_1_checked index (by omega) (by omega)
  else
    if cut : index < 358784 then
      exact segment_sound _ 358656 128 Update0700_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 358784 128 Update0700_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
