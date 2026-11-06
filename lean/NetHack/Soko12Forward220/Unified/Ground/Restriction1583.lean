import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1583_0_checked : (List.range' 810496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1583_1_checked : (List.range' 810624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1583_2_checked : (List.range' 810752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1583_3_checked : (List.range' 810880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1583_range (index : Nat) (lower : 810496 ≤ index) (upper : index < 811008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 810752 then
    if cut : index < 810624 then
      exact segment_sound _ 810496 128 Restriction1583_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 810624 128 Restriction1583_1_checked index (by omega) (by omega)
  else
    if cut : index < 810880 then
      exact segment_sound _ 810752 128 Restriction1583_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 810880 128 Restriction1583_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
