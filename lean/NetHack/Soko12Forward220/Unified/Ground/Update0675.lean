import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0675_0_checked : (List.range' 345600 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0675_1_checked : (List.range' 345728 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0675_2_checked : (List.range' 345856 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0675_3_checked : (List.range' 345984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0675_range (index : Nat) (lower : 345600 ≤ index) (upper : index < 346112) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 345856 then
    if cut : index < 345728 then
      exact segment_sound _ 345600 128 Update0675_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 345728 128 Update0675_1_checked index (by omega) (by omega)
  else
    if cut : index < 345984 then
      exact segment_sound _ 345856 128 Update0675_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 345984 128 Update0675_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
