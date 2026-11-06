import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0250_0_checked : (List.range' 128000 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0250_1_checked : (List.range' 128128 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0250_2_checked : (List.range' 128256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0250_3_checked : (List.range' 128384 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0250_range (index : Nat) (lower : 128000 ≤ index) (upper : index < 128512) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 128256 then
    if cut : index < 128128 then
      exact segment_sound _ 128000 128 Update0250_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 128128 128 Update0250_1_checked index (by omega) (by omega)
  else
    if cut : index < 128384 then
      exact segment_sound _ 128256 128 Update0250_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 128384 128 Update0250_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
