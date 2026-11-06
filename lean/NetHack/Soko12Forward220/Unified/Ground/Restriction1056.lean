import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1056_0_checked : (List.range' 540672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1056_1_checked : (List.range' 540800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1056_2_checked : (List.range' 540928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1056_3_checked : (List.range' 541056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1056_range (index : Nat) (lower : 540672 ≤ index) (upper : index < 541184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 540928 then
    if cut : index < 540800 then
      exact segment_sound _ 540672 128 Restriction1056_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 540800 128 Restriction1056_1_checked index (by omega) (by omega)
  else
    if cut : index < 541056 then
      exact segment_sound _ 540928 128 Restriction1056_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 541056 128 Restriction1056_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
