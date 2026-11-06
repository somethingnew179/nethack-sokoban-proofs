import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0485_0_checked : (List.range' 248320 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0485_1_checked : (List.range' 248448 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0485_2_checked : (List.range' 248576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0485_3_checked : (List.range' 248704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0485_range (index : Nat) (lower : 248320 ≤ index) (upper : index < 248832) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 248576 then
    if cut : index < 248448 then
      exact segment_sound _ 248320 128 Update0485_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 248448 128 Update0485_1_checked index (by omega) (by omega)
  else
    if cut : index < 248704 then
      exact segment_sound _ 248576 128 Update0485_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 248704 128 Update0485_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
