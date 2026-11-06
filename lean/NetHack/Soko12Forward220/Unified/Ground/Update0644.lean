import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0644_0_checked : (List.range' 329728 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0644_1_checked : (List.range' 329856 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0644_2_checked : (List.range' 329984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0644_3_checked : (List.range' 330112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0644_range (index : Nat) (lower : 329728 ≤ index) (upper : index < 330240) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 329984 then
    if cut : index < 329856 then
      exact segment_sound _ 329728 128 Update0644_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 329856 128 Update0644_1_checked index (by omega) (by omega)
  else
    if cut : index < 330112 then
      exact segment_sound _ 329984 128 Update0644_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 330112 128 Update0644_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
