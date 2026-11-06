import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0519_0_checked : (List.range' 265728 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0519_1_checked : (List.range' 265856 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0519_2_checked : (List.range' 265984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0519_3_checked : (List.range' 266112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0519_range (index : Nat) (lower : 265728 ≤ index) (upper : index < 266240) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 265984 then
    if cut : index < 265856 then
      exact segment_sound _ 265728 128 Update0519_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 265856 128 Update0519_1_checked index (by omega) (by omega)
  else
    if cut : index < 266112 then
      exact segment_sound _ 265984 128 Update0519_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 266112 128 Update0519_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
