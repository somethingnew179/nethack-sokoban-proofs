import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1213_0_checked : (List.range' 621056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1213_1_checked : (List.range' 621184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1213_2_checked : (List.range' 621312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1213_3_checked : (List.range' 621440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1213_range (index : Nat) (lower : 621056 ≤ index) (upper : index < 621568) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 621312 then
    if cut : index < 621184 then
      exact segment_sound _ 621056 128 Restriction1213_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 621184 128 Restriction1213_1_checked index (by omega) (by omega)
  else
    if cut : index < 621440 then
      exact segment_sound _ 621312 128 Restriction1213_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 621440 128 Restriction1213_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
