import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0604_0_checked : (List.range' 309248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0604_1_checked : (List.range' 309376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0604_2_checked : (List.range' 309504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0604_3_checked : (List.range' 309632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0604_range (index : Nat) (lower : 309248 ≤ index) (upper : index < 309760) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 309504 then
    if cut : index < 309376 then
      exact segment_sound _ 309248 128 Update0604_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 309376 128 Update0604_1_checked index (by omega) (by omega)
  else
    if cut : index < 309632 then
      exact segment_sound _ 309504 128 Update0604_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 309632 128 Update0604_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
