import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0035_0_checked : (List.range' 17920 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0035_1_checked : (List.range' 18048 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0035_2_checked : (List.range' 18176 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0035_3_checked : (List.range' 18304 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0035_range (index : Nat) (lower : 17920 ≤ index) (upper : index < 18432) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 18176 then
    if cut : index < 18048 then
      exact segment_sound _ 17920 128 Update0035_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 18048 128 Update0035_1_checked index (by omega) (by omega)
  else
    if cut : index < 18304 then
      exact segment_sound _ 18176 128 Update0035_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 18304 128 Update0035_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
