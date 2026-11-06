import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0471_0_checked : (List.range' 241152 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0471_1_checked : (List.range' 241280 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0471_2_checked : (List.range' 241408 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0471_3_checked : (List.range' 241536 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0471_range (index : Nat) (lower : 241152 ≤ index) (upper : index < 241664) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 241408 then
    if cut : index < 241280 then
      exact segment_sound _ 241152 128 Update0471_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 241280 128 Update0471_1_checked index (by omega) (by omega)
  else
    if cut : index < 241536 then
      exact segment_sound _ 241408 128 Update0471_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 241536 128 Update0471_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
