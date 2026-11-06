import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1044_0_checked : (List.range' 534528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1044_1_checked : (List.range' 534656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1044_2_checked : (List.range' 534784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1044_3_checked : (List.range' 534912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1044_range (index : Nat) (lower : 534528 ≤ index) (upper : index < 535040) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 534784 then
    if cut : index < 534656 then
      exact segment_sound _ 534528 128 Restriction1044_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 534656 128 Restriction1044_1_checked index (by omega) (by omega)
  else
    if cut : index < 534912 then
      exact segment_sound _ 534784 128 Restriction1044_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 534912 128 Restriction1044_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
