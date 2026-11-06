import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0542_0_checked : (List.range' 277504 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0542_1_checked : (List.range' 277632 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0542_2_checked : (List.range' 277760 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0542_3_checked : (List.range' 277888 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0542_range (index : Nat) (lower : 277504 ≤ index) (upper : index < 278016) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 277760 then
    if cut : index < 277632 then
      exact segment_sound _ 277504 128 Update0542_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 277632 128 Update0542_1_checked index (by omega) (by omega)
  else
    if cut : index < 277888 then
      exact segment_sound _ 277760 128 Update0542_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 277888 128 Update0542_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
