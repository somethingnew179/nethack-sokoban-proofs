import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0288_0_checked : (List.range' 147456 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0288_1_checked : (List.range' 147584 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0288_2_checked : (List.range' 147712 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0288_3_checked : (List.range' 147840 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0288_range (index : Nat) (lower : 147456 ≤ index) (upper : index < 147968) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 147712 then
    if cut : index < 147584 then
      exact segment_sound _ 147456 128 Update0288_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 147584 128 Update0288_1_checked index (by omega) (by omega)
  else
    if cut : index < 147840 then
      exact segment_sound _ 147712 128 Update0288_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 147840 128 Update0288_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
