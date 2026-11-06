import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0601_0_checked : (List.range' 307712 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0601_1_checked : (List.range' 307840 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0601_2_checked : (List.range' 307968 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0601_3_checked : (List.range' 308096 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0601_range (index : Nat) (lower : 307712 ≤ index) (upper : index < 308224) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 307968 then
    if cut : index < 307840 then
      exact segment_sound _ 307712 128 Update0601_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 307840 128 Update0601_1_checked index (by omega) (by omega)
  else
    if cut : index < 308096 then
      exact segment_sound _ 307968 128 Update0601_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 308096 128 Update0601_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
