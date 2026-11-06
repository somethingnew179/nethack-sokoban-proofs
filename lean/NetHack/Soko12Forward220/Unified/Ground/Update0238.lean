import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0238_0_checked : (List.range' 121856 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0238_1_checked : (List.range' 121984 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0238_2_checked : (List.range' 122112 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0238_3_checked : (List.range' 122240 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0238_range (index : Nat) (lower : 121856 ≤ index) (upper : index < 122368) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 122112 then
    if cut : index < 121984 then
      exact segment_sound _ 121856 128 Update0238_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 121984 128 Update0238_1_checked index (by omega) (by omega)
  else
    if cut : index < 122240 then
      exact segment_sound _ 122112 128 Update0238_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 122240 128 Update0238_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
