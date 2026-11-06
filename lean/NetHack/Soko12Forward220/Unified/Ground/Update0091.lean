import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0091_0_checked : (List.range' 46592 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0091_1_checked : (List.range' 46720 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0091_2_checked : (List.range' 46848 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0091_3_checked : (List.range' 46976 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0091_range (index : Nat) (lower : 46592 ≤ index) (upper : index < 47104) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 46848 then
    if cut : index < 46720 then
      exact segment_sound _ 46592 128 Update0091_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 46720 128 Update0091_1_checked index (by omega) (by omega)
  else
    if cut : index < 46976 then
      exact segment_sound _ 46848 128 Update0091_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 46976 128 Update0091_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
