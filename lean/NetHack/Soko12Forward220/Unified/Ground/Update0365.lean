import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0365_0_checked : (List.range' 186880 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0365_1_checked : (List.range' 187008 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0365_2_checked : (List.range' 187136 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0365_3_checked : (List.range' 187264 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0365_range (index : Nat) (lower : 186880 ≤ index) (upper : index < 187392) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 187136 then
    if cut : index < 187008 then
      exact segment_sound _ 186880 128 Update0365_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 187008 128 Update0365_1_checked index (by omega) (by omega)
  else
    if cut : index < 187264 then
      exact segment_sound _ 187136 128 Update0365_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 187264 128 Update0365_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
