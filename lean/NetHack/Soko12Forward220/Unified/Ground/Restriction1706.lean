import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1706_0_checked : (List.range' 873472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1706_1_checked : (List.range' 873600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1706_2_checked : (List.range' 873728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1706_3_checked : (List.range' 873856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1706_range (index : Nat) (lower : 873472 ≤ index) (upper : index < 873984) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 873728 then
    if cut : index < 873600 then
      exact segment_sound _ 873472 128 Restriction1706_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 873600 128 Restriction1706_1_checked index (by omega) (by omega)
  else
    if cut : index < 873856 then
      exact segment_sound _ 873728 128 Restriction1706_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 873856 128 Restriction1706_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
