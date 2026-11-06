import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0182_0_checked : (List.range' 93184 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0182_1_checked : (List.range' 93312 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0182_2_checked : (List.range' 93440 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0182_3_checked : (List.range' 93568 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0182_range (index : Nat) (lower : 93184 ≤ index) (upper : index < 93696) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 93440 then
    if cut : index < 93312 then
      exact segment_sound _ 93184 128 Update0182_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 93312 128 Update0182_1_checked index (by omega) (by omega)
  else
    if cut : index < 93568 then
      exact segment_sound _ 93440 128 Update0182_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 93568 128 Update0182_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
