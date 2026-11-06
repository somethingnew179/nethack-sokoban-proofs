import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0517_0_checked : (List.range' 264704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0517_1_checked : (List.range' 264832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0517_2_checked : (List.range' 264960 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0517_3_checked : (List.range' 265088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0517_range (index : Nat) (lower : 264704 ≤ index) (upper : index < 265216) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 264960 then
    if cut : index < 264832 then
      exact segment_sound _ 264704 128 Update0517_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 264832 128 Update0517_1_checked index (by omega) (by omega)
  else
    if cut : index < 265088 then
      exact segment_sound _ 264960 128 Update0517_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 265088 128 Update0517_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
