import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0251_0_checked : (List.range' 128512 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0251_1_checked : (List.range' 128640 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0251_2_checked : (List.range' 128768 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0251_3_checked : (List.range' 128896 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0251_range (index : Nat) (lower : 128512 ≤ index) (upper : index < 129024) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 128768 then
    if cut : index < 128640 then
      exact segment_sound _ 128512 128 Update0251_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 128640 128 Update0251_1_checked index (by omega) (by omega)
  else
    if cut : index < 128896 then
      exact segment_sound _ 128768 128 Update0251_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 128896 128 Update0251_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
