import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0570_0_checked : (List.range' 291840 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0570_1_checked : (List.range' 291968 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0570_2_checked : (List.range' 292096 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0570_3_checked : (List.range' 292224 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0570_range (index : Nat) (lower : 291840 ≤ index) (upper : index < 292352) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 292096 then
    if cut : index < 291968 then
      exact segment_sound _ 291840 128 Update0570_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 291968 128 Update0570_1_checked index (by omega) (by omega)
  else
    if cut : index < 292224 then
      exact segment_sound _ 292096 128 Update0570_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 292224 128 Update0570_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
