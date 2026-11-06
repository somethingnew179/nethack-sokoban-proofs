import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0484_0_checked : (List.range' 247808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0484_1_checked : (List.range' 247936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0484_2_checked : (List.range' 248064 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0484_3_checked : (List.range' 248192 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0484_range (index : Nat) (lower : 247808 ≤ index) (upper : index < 248320) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 248064 then
    if cut : index < 247936 then
      exact segment_sound _ 247808 128 Update0484_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 247936 128 Update0484_1_checked index (by omega) (by omega)
  else
    if cut : index < 248192 then
      exact segment_sound _ 248064 128 Update0484_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 248192 128 Update0484_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
