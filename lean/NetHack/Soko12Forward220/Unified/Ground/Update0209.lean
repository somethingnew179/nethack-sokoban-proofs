import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0209_0_checked : (List.range' 107008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0209_1_checked : (List.range' 107136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0209_2_checked : (List.range' 107264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0209_3_checked : (List.range' 107392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0209_range (index : Nat) (lower : 107008 ≤ index) (upper : index < 107520) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 107264 then
    if cut : index < 107136 then
      exact segment_sound _ 107008 128 Update0209_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 107136 128 Update0209_1_checked index (by omega) (by omega)
  else
    if cut : index < 107392 then
      exact segment_sound _ 107264 128 Update0209_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 107392 128 Update0209_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
