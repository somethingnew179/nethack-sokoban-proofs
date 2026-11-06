import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1745_0_checked : (List.range' 893440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1745_1_checked : (List.range' 893568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1745_2_checked : (List.range' 893696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1745_3_checked : (List.range' 893824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1745_range (index : Nat) (lower : 893440 ≤ index) (upper : index < 893952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 893696 then
    if cut : index < 893568 then
      exact segment_sound _ 893440 128 Restriction1745_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 893568 128 Restriction1745_1_checked index (by omega) (by omega)
  else
    if cut : index < 893824 then
      exact segment_sound _ 893696 128 Restriction1745_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 893824 128 Restriction1745_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
