import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0516_0_checked : (List.range' 264192 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0516_1_checked : (List.range' 264320 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0516_2_checked : (List.range' 264448 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0516_3_checked : (List.range' 264576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0516_range (index : Nat) (lower : 264192 ≤ index) (upper : index < 264704) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 264448 then
    if cut : index < 264320 then
      exact segment_sound _ 264192 128 Update0516_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 264320 128 Update0516_1_checked index (by omega) (by omega)
  else
    if cut : index < 264576 then
      exact segment_sound _ 264448 128 Update0516_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 264576 128 Update0516_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
