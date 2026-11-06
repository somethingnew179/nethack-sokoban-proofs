import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0095_0_checked : (List.range' 48640 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0095_1_checked : (List.range' 48768 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0095_2_checked : (List.range' 48896 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0095_3_checked : (List.range' 49024 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0095_range (index : Nat) (lower : 48640 ≤ index) (upper : index < 49152) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 48896 then
    if cut : index < 48768 then
      exact segment_sound _ 48640 128 Update0095_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 48768 128 Update0095_1_checked index (by omega) (by omega)
  else
    if cut : index < 49024 then
      exact segment_sound _ 48896 128 Update0095_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 49024 128 Update0095_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
