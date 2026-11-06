import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Update0110_0_checked : (List.range' 56320 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0110_1_checked : (List.range' 56448 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0110_2_checked : (List.range' 56576 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0110_3_checked : (List.range' 56704 128).all (fun index => DecisionDAGTransform.updateCheck read cells updates index) = true := by decide +kernel
theorem Update0110_range (index : Nat) (lower : 56320 ≤ index) (upper : index < 56832) : DecisionDAGTransform.updateCheck read cells updates index = true := by
  if cut : index < 56576 then
    if cut : index < 56448 then
      exact segment_sound _ 56320 128 Update0110_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 56448 128 Update0110_1_checked index (by omega) (by omega)
  else
    if cut : index < 56704 then
      exact segment_sound _ 56576 128 Update0110_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 56704 128 Update0110_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
