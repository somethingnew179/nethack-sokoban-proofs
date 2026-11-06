import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0656_0_checked : (List.range' 335872 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0656_1_checked : (List.range' 336000 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0656_2_checked : (List.range' 336128 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0656_3_checked : (List.range' 336256 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0656_range (index : Nat) (lower : 335872 ≤ index) (upper : index < 336384) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 336128 then
    if cut : index < 336000 then
      exact segment_sound _ 335872 128 Update0656_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 336000 128 Update0656_1_checked index (by omega) (by omega)
  else
    if cut : index < 336256 then
      exact segment_sound _ 336128 128 Update0656_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 336256 128 Update0656_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
