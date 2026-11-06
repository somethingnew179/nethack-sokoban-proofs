import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0334_0_checked : (List.range' 171008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0334_1_checked : (List.range' 171136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0334_2_checked : (List.range' 171264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0334_3_checked : (List.range' 171392 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0334_range (index : Nat) (lower : 171008 ≤ index) (upper : index < 171520) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 171264 then
    if cut : index < 171136 then
      exact segment_sound _ 171008 128 Update0334_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 171136 128 Update0334_1_checked index (by omega) (by omega)
  else
    if cut : index < 171392 then
      exact segment_sound _ 171264 128 Update0334_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 171392 128 Update0334_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
