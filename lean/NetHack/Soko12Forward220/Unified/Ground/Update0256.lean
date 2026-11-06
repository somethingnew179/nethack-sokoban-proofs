import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0256_0_checked : (List.range' 131072 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0256_1_checked : (List.range' 131200 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0256_2_checked : (List.range' 131328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0256_3_checked : (List.range' 131456 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0256_range (index : Nat) (lower : 131072 ≤ index) (upper : index < 131584) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 131328 then
    if cut : index < 131200 then
      exact segment_sound _ 131072 128 Update0256_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 131200 128 Update0256_1_checked index (by omega) (by omega)
  else
    if cut : index < 131456 then
      exact segment_sound _ 131328 128 Update0256_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 131456 128 Update0256_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
