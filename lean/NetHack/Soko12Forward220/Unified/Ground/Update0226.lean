import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0226_0_checked : (List.range' 115712 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0226_1_checked : (List.range' 115840 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0226_2_checked : (List.range' 115968 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0226_3_checked : (List.range' 116096 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0226_range (index : Nat) (lower : 115712 ≤ index) (upper : index < 116224) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 115968 then
    if cut : index < 115840 then
      exact segment_sound _ 115712 128 Update0226_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 115840 128 Update0226_1_checked index (by omega) (by omega)
  else
    if cut : index < 116096 then
      exact segment_sound _ 115968 128 Update0226_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 116096 128 Update0226_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
