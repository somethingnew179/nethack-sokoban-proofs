import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1650_0_checked : (List.range' 844800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1650_1_checked : (List.range' 844928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1650_2_checked : (List.range' 845056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1650_3_checked : (List.range' 845184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1650_range (index : Nat) (lower : 844800 ≤ index) (upper : index < 845312) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 845056 then
    if cut : index < 844928 then
      exact segment_sound _ 844800 128 Restriction1650_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 844928 128 Restriction1650_1_checked index (by omega) (by omega)
  else
    if cut : index < 845184 then
      exact segment_sound _ 845056 128 Restriction1650_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 845184 128 Restriction1650_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
