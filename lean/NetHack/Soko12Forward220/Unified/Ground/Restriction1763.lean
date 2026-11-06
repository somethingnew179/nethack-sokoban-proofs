import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1763_0_checked : (List.range' 902656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1763_1_checked : (List.range' 902784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1763_2_checked : (List.range' 902912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1763_3_checked : (List.range' 903040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1763_range (index : Nat) (lower : 902656 ≤ index) (upper : index < 903168) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 902912 then
    if cut : index < 902784 then
      exact segment_sound _ 902656 128 Restriction1763_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 902784 128 Restriction1763_1_checked index (by omega) (by omega)
  else
    if cut : index < 903040 then
      exact segment_sound _ 902912 128 Restriction1763_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 903040 128 Restriction1763_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
