import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0010_0_checked : (List.range' 5120 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0010_1_checked : (List.range' 5248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0010_2_checked : (List.range' 5376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0010_3_checked : (List.range' 5504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0010_range (index : Nat) (lower : 5120 ≤ index) (upper : index < 5632) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 5376 then
    if cut : index < 5248 then
      exact segment_sound _ 5120 128 Update0010_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 5248 128 Update0010_1_checked index (by omega) (by omega)
  else
    if cut : index < 5504 then
      exact segment_sound _ 5376 128 Update0010_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 5504 128 Update0010_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
