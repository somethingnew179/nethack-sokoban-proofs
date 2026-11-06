import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0510_0_checked : (List.range' 261120 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0510_1_checked : (List.range' 261248 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0510_2_checked : (List.range' 261376 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0510_3_checked : (List.range' 261504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0510_range (index : Nat) (lower : 261120 ≤ index) (upper : index < 261632) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 261376 then
    if cut : index < 261248 then
      exact segment_sound _ 261120 128 Update0510_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 261248 128 Update0510_1_checked index (by omega) (by omega)
  else
    if cut : index < 261504 then
      exact segment_sound _ 261376 128 Update0510_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 261504 128 Update0510_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
