import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1694_0_checked : (List.range' 867328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1694_1_checked : (List.range' 867456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1694_2_checked : (List.range' 867584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1694_3_checked : (List.range' 867712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1694_range (index : Nat) (lower : 867328 ≤ index) (upper : index < 867840) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 867584 then
    if cut : index < 867456 then
      exact segment_sound _ 867328 128 Restriction1694_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 867456 128 Restriction1694_1_checked index (by omega) (by omega)
  else
    if cut : index < 867712 then
      exact segment_sound _ 867584 128 Restriction1694_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 867712 128 Restriction1694_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
