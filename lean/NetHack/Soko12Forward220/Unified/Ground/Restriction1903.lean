import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1903_0_checked : (List.range' 974336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1903_1_checked : (List.range' 974464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1903_2_checked : (List.range' 974592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1903_3_checked : (List.range' 974720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1903_range (index : Nat) (lower : 974336 ≤ index) (upper : index < 974848) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 974592 then
    if cut : index < 974464 then
      exact segment_sound _ 974336 128 Restriction1903_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 974464 128 Restriction1903_1_checked index (by omega) (by omega)
  else
    if cut : index < 974720 then
      exact segment_sound _ 974592 128 Restriction1903_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 974720 128 Restriction1903_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
