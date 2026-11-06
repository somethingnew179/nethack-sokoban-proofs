import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0359_0_checked : (List.range' 183808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0359_1_checked : (List.range' 183936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0359_2_checked : (List.range' 184064 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0359_3_checked : (List.range' 184192 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0359_range (index : Nat) (lower : 183808 ≤ index) (upper : index < 184320) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 184064 then
    if cut : index < 183936 then
      exact segment_sound _ 183808 128 Update0359_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 183936 128 Update0359_1_checked index (by omega) (by omega)
  else
    if cut : index < 184192 then
      exact segment_sound _ 184064 128 Update0359_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 184192 128 Update0359_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
