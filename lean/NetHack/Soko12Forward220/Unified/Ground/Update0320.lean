import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0320_0_checked : (List.range' 163840 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0320_1_checked : (List.range' 163968 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0320_2_checked : (List.range' 164096 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0320_3_checked : (List.range' 164224 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0320_range (index : Nat) (lower : 163840 ≤ index) (upper : index < 164352) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 164096 then
    if cut : index < 163968 then
      exact segment_sound _ 163840 128 Update0320_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 163968 128 Update0320_1_checked index (by omega) (by omega)
  else
    if cut : index < 164224 then
      exact segment_sound _ 164096 128 Update0320_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 164224 128 Update0320_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
