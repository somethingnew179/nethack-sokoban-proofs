import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1902_0_checked : (List.range' 973824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1902_1_checked : (List.range' 973952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1902_2_checked : (List.range' 974080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1902_3_checked : (List.range' 974208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1902_range (index : Nat) (lower : 973824 ≤ index) (upper : index < 974336) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 974080 then
    if cut : index < 973952 then
      exact segment_sound _ 973824 128 Restriction1902_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 973952 128 Restriction1902_1_checked index (by omega) (by omega)
  else
    if cut : index < 974208 then
      exact segment_sound _ 974080 128 Restriction1902_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 974208 128 Restriction1902_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
