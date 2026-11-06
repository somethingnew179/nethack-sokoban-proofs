import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1381_0_checked : (List.range' 707072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1381_1_checked : (List.range' 707200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1381_2_checked : (List.range' 707328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1381_3_checked : (List.range' 707456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1381_range (index : Nat) (lower : 707072 ≤ index) (upper : index < 707584) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 707328 then
    if cut : index < 707200 then
      exact segment_sound _ 707072 128 Restriction1381_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 707200 128 Restriction1381_1_checked index (by omega) (by omega)
  else
    if cut : index < 707456 then
      exact segment_sound _ 707328 128 Restriction1381_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 707456 128 Restriction1381_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
