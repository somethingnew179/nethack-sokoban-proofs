import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1973_0_checked : (List.range' 1010176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1973_1_checked : (List.range' 1010304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1973_2_checked : (List.range' 1010432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1973_3_checked : (List.range' 1010560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1973_range (index : Nat) (lower : 1010176 ≤ index) (upper : index < 1010688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1010432 then
    if cut : index < 1010304 then
      exact segment_sound _ 1010176 128 Restriction1973_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1010304 128 Restriction1973_1_checked index (by omega) (by omega)
  else
    if cut : index < 1010560 then
      exact segment_sound _ 1010432 128 Restriction1973_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1010560 128 Restriction1973_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
