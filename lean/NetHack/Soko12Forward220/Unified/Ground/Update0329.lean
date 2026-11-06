import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0329_0_checked : (List.range' 168448 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0329_1_checked : (List.range' 168576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0329_2_checked : (List.range' 168704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0329_3_checked : (List.range' 168832 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0329_range (index : Nat) (lower : 168448 ≤ index) (upper : index < 168960) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 168704 then
    if cut : index < 168576 then
      exact segment_sound _ 168448 128 Update0329_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 168576 128 Update0329_1_checked index (by omega) (by omega)
  else
    if cut : index < 168832 then
      exact segment_sound _ 168704 128 Update0329_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 168832 128 Update0329_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
