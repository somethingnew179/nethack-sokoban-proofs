import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0328_0_checked : (List.range' 167936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0328_1_checked : (List.range' 168064 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0328_2_checked : (List.range' 168192 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0328_3_checked : (List.range' 168320 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0328_range (index : Nat) (lower : 167936 ≤ index) (upper : index < 168448) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 168192 then
    if cut : index < 168064 then
      exact segment_sound _ 167936 128 Update0328_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 168064 128 Update0328_1_checked index (by omega) (by omega)
  else
    if cut : index < 168320 then
      exact segment_sound _ 168192 128 Update0328_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 168320 128 Update0328_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
