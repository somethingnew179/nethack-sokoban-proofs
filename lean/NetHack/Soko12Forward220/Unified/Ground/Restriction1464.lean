import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1464_0_checked : (List.range' 749568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1464_1_checked : (List.range' 749696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1464_2_checked : (List.range' 749824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1464_3_checked : (List.range' 749952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1464_range (index : Nat) (lower : 749568 ≤ index) (upper : index < 750080) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 749824 then
    if cut : index < 749696 then
      exact segment_sound _ 749568 128 Restriction1464_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 749696 128 Restriction1464_1_checked index (by omega) (by omega)
  else
    if cut : index < 749952 then
      exact segment_sound _ 749824 128 Restriction1464_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 749952 128 Restriction1464_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
