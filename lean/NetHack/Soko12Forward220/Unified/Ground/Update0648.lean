import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0648_0_checked : (List.range' 331776 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0648_1_checked : (List.range' 331904 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0648_2_checked : (List.range' 332032 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0648_3_checked : (List.range' 332160 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0648_range (index : Nat) (lower : 331776 ≤ index) (upper : index < 332288) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 332032 then
    if cut : index < 331904 then
      exact segment_sound _ 331776 128 Update0648_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 331904 128 Update0648_1_checked index (by omega) (by omega)
  else
    if cut : index < 332160 then
      exact segment_sound _ 332032 128 Update0648_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 332160 128 Update0648_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
