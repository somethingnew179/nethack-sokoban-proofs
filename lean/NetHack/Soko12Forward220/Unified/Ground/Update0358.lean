import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0358_0_checked : (List.range' 183296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0358_1_checked : (List.range' 183424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0358_2_checked : (List.range' 183552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0358_3_checked : (List.range' 183680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0358_range (index : Nat) (lower : 183296 ≤ index) (upper : index < 183808) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 183552 then
    if cut : index < 183424 then
      exact segment_sound _ 183296 128 Update0358_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 183424 128 Update0358_1_checked index (by omega) (by omega)
  else
    if cut : index < 183680 then
      exact segment_sound _ 183552 128 Update0358_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 183680 128 Update0358_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
