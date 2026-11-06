import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1621_0_checked : (List.range' 829952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1621_1_checked : (List.range' 830080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1621_2_checked : (List.range' 830208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1621_3_checked : (List.range' 830336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1621_range (index : Nat) (lower : 829952 ≤ index) (upper : index < 830464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 830208 then
    if cut : index < 830080 then
      exact segment_sound _ 829952 128 Restriction1621_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 830080 128 Restriction1621_1_checked index (by omega) (by omega)
  else
    if cut : index < 830336 then
      exact segment_sound _ 830208 128 Restriction1621_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 830336 128 Restriction1621_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
