import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1121_0_checked : (List.range' 573952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1121_1_checked : (List.range' 574080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1121_2_checked : (List.range' 574208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1121_3_checked : (List.range' 574336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1121_range (index : Nat) (lower : 573952 ≤ index) (upper : index < 574464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 574208 then
    if cut : index < 574080 then
      exact segment_sound _ 573952 128 Restriction1121_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 574080 128 Restriction1121_1_checked index (by omega) (by omega)
  else
    if cut : index < 574336 then
      exact segment_sound _ 574208 128 Restriction1121_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 574336 128 Restriction1121_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
