import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1871_0_checked : (List.range' 957952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1871_1_checked : (List.range' 958080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1871_2_checked : (List.range' 958208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1871_3_checked : (List.range' 958336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1871_range (index : Nat) (lower : 957952 ≤ index) (upper : index < 958464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 958208 then
    if cut : index < 958080 then
      exact segment_sound _ 957952 128 Restriction1871_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 958080 128 Restriction1871_1_checked index (by omega) (by omega)
  else
    if cut : index < 958336 then
      exact segment_sound _ 958208 128 Restriction1871_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 958336 128 Restriction1871_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
