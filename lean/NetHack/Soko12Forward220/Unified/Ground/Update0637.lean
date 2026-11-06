import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0637_0_checked : (List.range' 326144 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0637_1_checked : (List.range' 326272 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0637_2_checked : (List.range' 326400 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0637_3_checked : (List.range' 326528 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0637_range (index : Nat) (lower : 326144 ≤ index) (upper : index < 326656) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 326400 then
    if cut : index < 326272 then
      exact segment_sound _ 326144 128 Update0637_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 326272 128 Update0637_1_checked index (by omega) (by omega)
  else
    if cut : index < 326528 then
      exact segment_sound _ 326400 128 Update0637_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 326528 128 Update0637_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
