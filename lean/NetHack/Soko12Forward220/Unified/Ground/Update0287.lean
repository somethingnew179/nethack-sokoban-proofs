import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0287_0_checked : (List.range' 146944 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0287_1_checked : (List.range' 147072 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0287_2_checked : (List.range' 147200 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0287_3_checked : (List.range' 147328 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0287_range (index : Nat) (lower : 146944 ≤ index) (upper : index < 147456) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 147200 then
    if cut : index < 147072 then
      exact segment_sound _ 146944 128 Update0287_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 147072 128 Update0287_1_checked index (by omega) (by omega)
  else
    if cut : index < 147328 then
      exact segment_sound _ 147200 128 Update0287_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 147328 128 Update0287_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
