import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1896_0_checked : (List.range' 970752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1896_1_checked : (List.range' 970880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1896_2_checked : (List.range' 971008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1896_3_checked : (List.range' 971136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1896_range (index : Nat) (lower : 970752 ≤ index) (upper : index < 971264) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 971008 then
    if cut : index < 970880 then
      exact segment_sound _ 970752 128 Restriction1896_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 970880 128 Restriction1896_1_checked index (by omega) (by omega)
  else
    if cut : index < 971136 then
      exact segment_sound _ 971008 128 Restriction1896_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 971136 128 Restriction1896_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
