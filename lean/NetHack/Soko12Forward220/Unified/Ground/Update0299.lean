import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0299_0_checked : (List.range' 153088 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0299_1_checked : (List.range' 153216 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0299_2_checked : (List.range' 153344 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0299_3_checked : (List.range' 153472 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0299_range (index : Nat) (lower : 153088 ≤ index) (upper : index < 153600) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 153344 then
    if cut : index < 153216 then
      exact segment_sound _ 153088 128 Update0299_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 153216 128 Update0299_1_checked index (by omega) (by omega)
  else
    if cut : index < 153472 then
      exact segment_sound _ 153344 128 Update0299_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 153472 128 Update0299_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
