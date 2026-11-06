import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0478_0_checked : (List.range' 244736 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0478_1_checked : (List.range' 244864 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0478_2_checked : (List.range' 244992 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0478_3_checked : (List.range' 245120 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0478_range (index : Nat) (lower : 244736 ≤ index) (upper : index < 245248) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 244992 then
    if cut : index < 244864 then
      exact segment_sound _ 244736 128 Update0478_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 244864 128 Update0478_1_checked index (by omega) (by omega)
  else
    if cut : index < 245120 then
      exact segment_sound _ 244992 128 Update0478_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 245120 128 Update0478_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
