import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0670_0_checked : (List.range' 343040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0670_1_checked : (List.range' 343168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0670_2_checked : (List.range' 343296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0670_3_checked : (List.range' 343424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0670_range (index : Nat) (lower : 343040 ≤ index) (upper : index < 343552) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 343296 then
    if cut : index < 343168 then
      exact segment_sound _ 343040 128 Update0670_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 343168 128 Update0670_1_checked index (by omega) (by omega)
  else
    if cut : index < 343424 then
      exact segment_sound _ 343296 128 Update0670_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 343424 128 Update0670_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
