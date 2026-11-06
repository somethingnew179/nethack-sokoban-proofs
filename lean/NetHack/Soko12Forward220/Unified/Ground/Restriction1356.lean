import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1356_0_checked : (List.range' 694272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1356_1_checked : (List.range' 694400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1356_2_checked : (List.range' 694528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1356_3_checked : (List.range' 694656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1356_range (index : Nat) (lower : 694272 ≤ index) (upper : index < 694784) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 694528 then
    if cut : index < 694400 then
      exact segment_sound _ 694272 128 Restriction1356_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 694400 128 Restriction1356_1_checked index (by omega) (by omega)
  else
    if cut : index < 694656 then
      exact segment_sound _ 694528 128 Restriction1356_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 694656 128 Restriction1356_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
