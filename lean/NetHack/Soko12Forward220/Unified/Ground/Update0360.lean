import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0360_0_checked : (List.range' 184320 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0360_1_checked : (List.range' 184448 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0360_2_checked : (List.range' 184576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0360_3_checked : (List.range' 184704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0360_range (index : Nat) (lower : 184320 ≤ index) (upper : index < 184832) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 184576 then
    if cut : index < 184448 then
      exact segment_sound _ 184320 128 Update0360_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 184448 128 Update0360_1_checked index (by omega) (by omega)
  else
    if cut : index < 184704 then
      exact segment_sound _ 184576 128 Update0360_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 184704 128 Update0360_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
