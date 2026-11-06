import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0324_0_checked : (List.range' 165888 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0324_1_checked : (List.range' 166016 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0324_2_checked : (List.range' 166144 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0324_3_checked : (List.range' 166272 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0324_range (index : Nat) (lower : 165888 ≤ index) (upper : index < 166400) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 166144 then
    if cut : index < 166016 then
      exact segment_sound _ 165888 128 Update0324_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 166016 128 Update0324_1_checked index (by omega) (by omega)
  else
    if cut : index < 166272 then
      exact segment_sound _ 166144 128 Update0324_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 166272 128 Update0324_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
