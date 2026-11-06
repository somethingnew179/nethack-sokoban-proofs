import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0668_0_checked : (List.range' 342016 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0668_1_checked : (List.range' 342144 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0668_2_checked : (List.range' 342272 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0668_3_checked : (List.range' 342400 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0668_range (index : Nat) (lower : 342016 ≤ index) (upper : index < 342528) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 342272 then
    if cut : index < 342144 then
      exact segment_sound _ 342016 128 Update0668_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 342144 128 Update0668_1_checked index (by omega) (by omega)
  else
    if cut : index < 342400 then
      exact segment_sound _ 342272 128 Update0668_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 342400 128 Update0668_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
