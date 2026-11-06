import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0362_0_checked : (List.range' 185344 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0362_1_checked : (List.range' 185472 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0362_2_checked : (List.range' 185600 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0362_3_checked : (List.range' 185728 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0362_range (index : Nat) (lower : 185344 ≤ index) (upper : index < 185856) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 185600 then
    if cut : index < 185472 then
      exact segment_sound _ 185344 128 Update0362_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 185472 128 Update0362_1_checked index (by omega) (by omega)
  else
    if cut : index < 185728 then
      exact segment_sound _ 185600 128 Update0362_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 185728 128 Update0362_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
