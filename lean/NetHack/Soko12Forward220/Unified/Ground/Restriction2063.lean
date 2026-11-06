import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2063_0_checked : (List.range' 1056256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2063_1_checked : (List.range' 1056384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2063_2_checked : (List.range' 1056512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2063_3_checked : (List.range' 1056640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2063_range (index : Nat) (lower : 1056256 ≤ index) (upper : index < 1056768) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1056512 then
    if cut : index < 1056384 then
      exact segment_sound _ 1056256 128 Restriction2063_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1056384 128 Restriction2063_1_checked index (by omega) (by omega)
  else
    if cut : index < 1056640 then
      exact segment_sound _ 1056512 128 Restriction2063_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1056640 128 Restriction2063_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
