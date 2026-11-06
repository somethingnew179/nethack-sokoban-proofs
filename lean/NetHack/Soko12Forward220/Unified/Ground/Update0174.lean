import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0174_0_checked : (List.range' 89088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0174_1_checked : (List.range' 89216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0174_2_checked : (List.range' 89344 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0174_3_checked : (List.range' 89472 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0174_range (index : Nat) (lower : 89088 ≤ index) (upper : index < 89600) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 89344 then
    if cut : index < 89216 then
      exact segment_sound _ 89088 128 Update0174_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 89216 128 Update0174_1_checked index (by omega) (by omega)
  else
    if cut : index < 89472 then
      exact segment_sound _ 89344 128 Update0174_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 89472 128 Update0174_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
