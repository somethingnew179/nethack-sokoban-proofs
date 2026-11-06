import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1777_0_checked : (List.range' 909824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1777_1_checked : (List.range' 909952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1777_2_checked : (List.range' 910080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1777_3_checked : (List.range' 910208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1777_range (index : Nat) (lower : 909824 ≤ index) (upper : index < 910336) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 910080 then
    if cut : index < 909952 then
      exact segment_sound _ 909824 128 Restriction1777_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 909952 128 Restriction1777_1_checked index (by omega) (by omega)
  else
    if cut : index < 910208 then
      exact segment_sound _ 910080 128 Restriction1777_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 910208 128 Restriction1777_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
