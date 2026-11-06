import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0511_0_checked : (List.range' 261632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0511_1_checked : (List.range' 261760 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0511_2_checked : (List.range' 261888 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0511_3_checked : (List.range' 262016 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0511_range (index : Nat) (lower : 261632 ≤ index) (upper : index < 262144) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 261888 then
    if cut : index < 261760 then
      exact segment_sound _ 261632 128 Update0511_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 261760 128 Update0511_1_checked index (by omega) (by omega)
  else
    if cut : index < 262016 then
      exact segment_sound _ 261888 128 Update0511_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 262016 128 Update0511_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
