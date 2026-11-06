import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0733_0_checked : (List.range' 375296 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0733_1_checked : (List.range' 375424 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0733_2_checked : (List.range' 375552 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0733_3_checked : (List.range' 375680 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0733_range (index : Nat) (lower : 375296 ≤ index) (upper : index < 375808) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 375552 then
    if cut : index < 375424 then
      exact segment_sound _ 375296 128 Update0733_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 375424 128 Update0733_1_checked index (by omega) (by omega)
  else
    if cut : index < 375680 then
      exact segment_sound _ 375552 128 Update0733_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 375680 128 Update0733_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
