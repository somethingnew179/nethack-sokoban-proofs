import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0671_0_checked : (List.range' 343552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0671_1_checked : (List.range' 343680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0671_2_checked : (List.range' 343808 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0671_3_checked : (List.range' 343936 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0671_range (index : Nat) (lower : 343552 ≤ index) (upper : index < 344064) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 343808 then
    if cut : index < 343680 then
      exact segment_sound _ 343552 128 Update0671_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 343680 128 Update0671_1_checked index (by omega) (by omega)
  else
    if cut : index < 343936 then
      exact segment_sound _ 343808 128 Update0671_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 343936 128 Update0671_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
