import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2040_0_checked : (List.range' 1044480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2040_1_checked : (List.range' 1044608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2040_2_checked : (List.range' 1044736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2040_3_checked : (List.range' 1044864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2040_range (index : Nat) (lower : 1044480 ≤ index) (upper : index < 1044992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1044736 then
    if cut : index < 1044608 then
      exact segment_sound _ 1044480 128 Restriction2040_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1044608 128 Restriction2040_1_checked index (by omega) (by omega)
  else
    if cut : index < 1044864 then
      exact segment_sound _ 1044736 128 Restriction2040_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1044864 128 Restriction2040_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
