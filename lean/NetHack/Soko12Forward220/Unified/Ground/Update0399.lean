import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0399_0_checked : (List.range' 204288 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0399_1_checked : (List.range' 204416 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0399_2_checked : (List.range' 204544 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0399_3_checked : (List.range' 204672 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0399_range (index : Nat) (lower : 204288 ≤ index) (upper : index < 204800) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 204544 then
    if cut : index < 204416 then
      exact segment_sound _ 204288 128 Update0399_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 204416 128 Update0399_1_checked index (by omega) (by omega)
  else
    if cut : index < 204672 then
      exact segment_sound _ 204544 128 Update0399_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 204672 128 Update0399_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
