import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0074_0_checked : (List.range' 37888 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0074_1_checked : (List.range' 38016 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0074_2_checked : (List.range' 38144 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0074_3_checked : (List.range' 38272 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0074_range (index : Nat) (lower : 37888 ≤ index) (upper : index < 38400) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 38144 then
    if cut : index < 38016 then
      exact segment_sound _ 37888 128 Update0074_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 38016 128 Update0074_1_checked index (by omega) (by omega)
  else
    if cut : index < 38272 then
      exact segment_sound _ 38144 128 Update0074_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 38272 128 Update0074_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
