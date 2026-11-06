import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1374_0_checked : (List.range' 703488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1374_1_checked : (List.range' 703616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1374_2_checked : (List.range' 703744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1374_3_checked : (List.range' 703872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1374_range (index : Nat) (lower : 703488 ≤ index) (upper : index < 704000) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 703744 then
    if cut : index < 703616 then
      exact segment_sound _ 703488 128 Restriction1374_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 703616 128 Restriction1374_1_checked index (by omega) (by omega)
  else
    if cut : index < 703872 then
      exact segment_sound _ 703744 128 Restriction1374_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 703872 128 Restriction1374_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
