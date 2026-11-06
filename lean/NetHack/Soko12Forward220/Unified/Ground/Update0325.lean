import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0325_0_checked : (List.range' 166400 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0325_1_checked : (List.range' 166528 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0325_2_checked : (List.range' 166656 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0325_3_checked : (List.range' 166784 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0325_range (index : Nat) (lower : 166400 ≤ index) (upper : index < 166912) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 166656 then
    if cut : index < 166528 then
      exact segment_sound _ 166400 128 Update0325_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 166528 128 Update0325_1_checked index (by omega) (by omega)
  else
    if cut : index < 166784 then
      exact segment_sound _ 166656 128 Update0325_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 166784 128 Update0325_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
