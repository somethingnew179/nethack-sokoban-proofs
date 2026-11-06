import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0076_0_checked : (List.range' 38912 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0076_1_checked : (List.range' 39040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0076_2_checked : (List.range' 39168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0076_3_checked : (List.range' 39296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0076_range (index : Nat) (lower : 38912 ≤ index) (upper : index < 39424) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 39168 then
    if cut : index < 39040 then
      exact segment_sound _ 38912 128 Update0076_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 39040 128 Update0076_1_checked index (by omega) (by omega)
  else
    if cut : index < 39296 then
      exact segment_sound _ 39168 128 Update0076_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 39296 128 Update0076_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
