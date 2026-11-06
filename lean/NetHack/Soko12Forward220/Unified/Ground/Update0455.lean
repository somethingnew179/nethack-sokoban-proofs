import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0455_0_checked : (List.range' 232960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0455_1_checked : (List.range' 233088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0455_2_checked : (List.range' 233216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0455_3_checked : (List.range' 233344 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0455_range (index : Nat) (lower : 232960 ≤ index) (upper : index < 233472) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 233216 then
    if cut : index < 233088 then
      exact segment_sound _ 232960 128 Update0455_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 233088 128 Update0455_1_checked index (by omega) (by omega)
  else
    if cut : index < 233344 then
      exact segment_sound _ 233216 128 Update0455_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 233344 128 Update0455_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
