import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1744_0_checked : (List.range' 892928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1744_1_checked : (List.range' 893056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1744_2_checked : (List.range' 893184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1744_3_checked : (List.range' 893312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1744_range (index : Nat) (lower : 892928 ≤ index) (upper : index < 893440) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 893184 then
    if cut : index < 893056 then
      exact segment_sound _ 892928 128 Restriction1744_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 893056 128 Restriction1744_1_checked index (by omega) (by omega)
  else
    if cut : index < 893312 then
      exact segment_sound _ 893184 128 Restriction1744_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 893312 128 Restriction1744_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
