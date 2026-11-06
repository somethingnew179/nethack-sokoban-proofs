import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0504_0_checked : (List.range' 258048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0504_1_checked : (List.range' 258176 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0504_2_checked : (List.range' 258304 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0504_3_checked : (List.range' 258432 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0504_range (index : Nat) (lower : 258048 ≤ index) (upper : index < 258560) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 258304 then
    if cut : index < 258176 then
      exact segment_sound _ 258048 128 Update0504_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 258176 128 Update0504_1_checked index (by omega) (by omega)
  else
    if cut : index < 258432 then
      exact segment_sound _ 258304 128 Update0504_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 258432 128 Update0504_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
