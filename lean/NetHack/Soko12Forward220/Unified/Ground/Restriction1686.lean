import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1686_0_checked : (List.range' 863232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1686_1_checked : (List.range' 863360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1686_2_checked : (List.range' 863488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1686_3_checked : (List.range' 863616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1686_range (index : Nat) (lower : 863232 ≤ index) (upper : index < 863744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 863488 then
    if cut : index < 863360 then
      exact segment_sound _ 863232 128 Restriction1686_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 863360 128 Restriction1686_1_checked index (by omega) (by omega)
  else
    if cut : index < 863616 then
      exact segment_sound _ 863488 128 Restriction1686_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 863616 128 Restriction1686_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
