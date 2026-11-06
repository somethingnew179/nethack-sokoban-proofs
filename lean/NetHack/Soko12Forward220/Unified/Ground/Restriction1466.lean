import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1466_0_checked : (List.range' 750592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1466_1_checked : (List.range' 750720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1466_2_checked : (List.range' 750848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1466_3_checked : (List.range' 750976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1466_range (index : Nat) (lower : 750592 ≤ index) (upper : index < 751104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 750848 then
    if cut : index < 750720 then
      exact segment_sound _ 750592 128 Restriction1466_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 750720 128 Restriction1466_1_checked index (by omega) (by omega)
  else
    if cut : index < 750976 then
      exact segment_sound _ 750848 128 Restriction1466_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 750976 128 Restriction1466_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
