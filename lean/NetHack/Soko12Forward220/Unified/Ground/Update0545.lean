import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0545_0_checked : (List.range' 279040 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0545_1_checked : (List.range' 279168 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0545_2_checked : (List.range' 279296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0545_3_checked : (List.range' 279424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0545_range (index : Nat) (lower : 279040 ≤ index) (upper : index < 279552) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 279296 then
    if cut : index < 279168 then
      exact segment_sound _ 279040 128 Update0545_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 279168 128 Update0545_1_checked index (by omega) (by omega)
  else
    if cut : index < 279424 then
      exact segment_sound _ 279296 128 Update0545_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 279424 128 Update0545_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
