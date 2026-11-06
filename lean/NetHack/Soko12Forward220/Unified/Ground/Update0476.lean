import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0476_0_checked : (List.range' 243712 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0476_1_checked : (List.range' 243840 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0476_2_checked : (List.range' 243968 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0476_3_checked : (List.range' 244096 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0476_range (index : Nat) (lower : 243712 ≤ index) (upper : index < 244224) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 243968 then
    if cut : index < 243840 then
      exact segment_sound _ 243712 128 Update0476_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 243840 128 Update0476_1_checked index (by omega) (by omega)
  else
    if cut : index < 244096 then
      exact segment_sound _ 243968 128 Update0476_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 244096 128 Update0476_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
