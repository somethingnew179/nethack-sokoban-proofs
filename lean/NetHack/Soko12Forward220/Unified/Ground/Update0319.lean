import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0319_0_checked : (List.range' 163328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0319_1_checked : (List.range' 163456 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0319_2_checked : (List.range' 163584 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0319_3_checked : (List.range' 163712 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0319_range (index : Nat) (lower : 163328 ≤ index) (upper : index < 163840) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 163584 then
    if cut : index < 163456 then
      exact segment_sound _ 163328 128 Update0319_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 163456 128 Update0319_1_checked index (by omega) (by omega)
  else
    if cut : index < 163712 then
      exact segment_sound _ 163584 128 Update0319_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 163712 128 Update0319_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
