import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1146_0_checked : (List.range' 586752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1146_1_checked : (List.range' 586880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1146_2_checked : (List.range' 587008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1146_3_checked : (List.range' 587136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1146_range (index : Nat) (lower : 586752 ≤ index) (upper : index < 587264) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 587008 then
    if cut : index < 586880 then
      exact segment_sound _ 586752 128 Restriction1146_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 586880 128 Restriction1146_1_checked index (by omega) (by omega)
  else
    if cut : index < 587136 then
      exact segment_sound _ 587008 128 Restriction1146_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 587136 128 Restriction1146_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
