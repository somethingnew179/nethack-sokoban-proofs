import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1041_0_checked : (List.range' 532992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1041_1_checked : (List.range' 533120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1041_2_checked : (List.range' 533248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1041_3_checked : (List.range' 533376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1041_range (index : Nat) (lower : 532992 ≤ index) (upper : index < 533504) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 533248 then
    if cut : index < 533120 then
      exact segment_sound _ 532992 128 Restriction1041_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 533120 128 Restriction1041_1_checked index (by omega) (by omega)
  else
    if cut : index < 533376 then
      exact segment_sound _ 533248 128 Restriction1041_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 533376 128 Restriction1041_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
