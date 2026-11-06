import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0367_0_checked : (List.range' 187904 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0367_1_checked : (List.range' 188032 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0367_2_checked : (List.range' 188160 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0367_3_checked : (List.range' 188288 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0367_range (index : Nat) (lower : 187904 ≤ index) (upper : index < 188416) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 188160 then
    if cut : index < 188032 then
      exact segment_sound _ 187904 128 Update0367_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 188032 128 Update0367_1_checked index (by omega) (by omega)
  else
    if cut : index < 188288 then
      exact segment_sound _ 188160 128 Update0367_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 188288 128 Update0367_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
