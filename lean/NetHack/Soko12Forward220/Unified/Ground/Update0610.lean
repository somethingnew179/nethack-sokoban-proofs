import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0610_0_checked : (List.range' 312320 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0610_1_checked : (List.range' 312448 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0610_2_checked : (List.range' 312576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0610_3_checked : (List.range' 312704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0610_range (index : Nat) (lower : 312320 ≤ index) (upper : index < 312832) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 312576 then
    if cut : index < 312448 then
      exact segment_sound _ 312320 128 Update0610_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 312448 128 Update0610_1_checked index (by omega) (by omega)
  else
    if cut : index < 312704 then
      exact segment_sound _ 312576 128 Update0610_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 312704 128 Update0610_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
