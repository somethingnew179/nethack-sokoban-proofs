import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0621_0_checked : (List.range' 317952 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0621_1_checked : (List.range' 318080 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0621_2_checked : (List.range' 318208 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0621_3_checked : (List.range' 318336 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0621_range (index : Nat) (lower : 317952 ≤ index) (upper : index < 318464) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 318208 then
    if cut : index < 318080 then
      exact segment_sound _ 317952 128 Update0621_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 318080 128 Update0621_1_checked index (by omega) (by omega)
  else
    if cut : index < 318336 then
      exact segment_sound _ 318208 128 Update0621_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 318336 128 Update0621_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
