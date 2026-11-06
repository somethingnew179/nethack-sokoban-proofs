import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0047_0_checked : (List.range' 24064 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0047_1_checked : (List.range' 24192 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0047_2_checked : (List.range' 24320 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0047_3_checked : (List.range' 24448 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0047_range (index : Nat) (lower : 24064 ≤ index) (upper : index < 24576) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 24320 then
    if cut : index < 24192 then
      exact segment_sound _ 24064 128 Update0047_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 24192 128 Update0047_1_checked index (by omega) (by omega)
  else
    if cut : index < 24448 then
      exact segment_sound _ 24320 128 Update0047_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 24448 128 Update0047_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
