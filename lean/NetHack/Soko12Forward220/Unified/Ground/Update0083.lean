import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0083_0_checked : (List.range' 42496 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0083_1_checked : (List.range' 42624 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0083_2_checked : (List.range' 42752 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0083_3_checked : (List.range' 42880 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0083_range (index : Nat) (lower : 42496 ≤ index) (upper : index < 43008) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 42752 then
    if cut : index < 42624 then
      exact segment_sound _ 42496 128 Update0083_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 42624 128 Update0083_1_checked index (by omega) (by omega)
  else
    if cut : index < 42880 then
      exact segment_sound _ 42752 128 Update0083_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 42880 128 Update0083_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
