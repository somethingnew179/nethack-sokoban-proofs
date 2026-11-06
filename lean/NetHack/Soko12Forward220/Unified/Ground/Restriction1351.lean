import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1351_0_checked : (List.range' 691712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1351_1_checked : (List.range' 691840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1351_2_checked : (List.range' 691968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1351_3_checked : (List.range' 692096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1351_range (index : Nat) (lower : 691712 ≤ index) (upper : index < 692224) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 691968 then
    if cut : index < 691840 then
      exact segment_sound _ 691712 128 Restriction1351_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 691840 128 Restriction1351_1_checked index (by omega) (by omega)
  else
    if cut : index < 692096 then
      exact segment_sound _ 691968 128 Restriction1351_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 692096 128 Restriction1351_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
