import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0651_0_checked : (List.range' 333312 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0651_1_checked : (List.range' 333440 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0651_2_checked : (List.range' 333568 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0651_3_checked : (List.range' 333696 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0651_range (index : Nat) (lower : 333312 ≤ index) (upper : index < 333824) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 333568 then
    if cut : index < 333440 then
      exact segment_sound _ 333312 128 Update0651_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 333440 128 Update0651_1_checked index (by omega) (by omega)
  else
    if cut : index < 333696 then
      exact segment_sound _ 333568 128 Update0651_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 333696 128 Update0651_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
