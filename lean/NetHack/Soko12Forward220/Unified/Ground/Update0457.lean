import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0457_0_checked : (List.range' 233984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0457_1_checked : (List.range' 234112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0457_2_checked : (List.range' 234240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0457_3_checked : (List.range' 234368 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0457_range (index : Nat) (lower : 233984 ≤ index) (upper : index < 234496) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 234240 then
    if cut : index < 234112 then
      exact segment_sound _ 233984 128 Update0457_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 234112 128 Update0457_1_checked index (by omega) (by omega)
  else
    if cut : index < 234368 then
      exact segment_sound _ 234240 128 Update0457_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 234368 128 Update0457_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
