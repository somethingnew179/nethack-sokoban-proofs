import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0364_0_checked : (List.range' 186368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0364_1_checked : (List.range' 186496 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0364_2_checked : (List.range' 186624 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0364_3_checked : (List.range' 186752 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0364_range (index : Nat) (lower : 186368 ≤ index) (upper : index < 186880) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 186624 then
    if cut : index < 186496 then
      exact segment_sound _ 186368 128 Update0364_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 186496 128 Update0364_1_checked index (by omega) (by omega)
  else
    if cut : index < 186752 then
      exact segment_sound _ 186624 128 Update0364_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 186752 128 Update0364_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
