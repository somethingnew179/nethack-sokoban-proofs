import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1312_0_checked : (List.range' 671744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1312_1_checked : (List.range' 671872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1312_2_checked : (List.range' 672000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1312_3_checked : (List.range' 672128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1312_range (index : Nat) (lower : 671744 ≤ index) (upper : index < 672256) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 672000 then
    if cut : index < 671872 then
      exact segment_sound _ 671744 128 Restriction1312_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 671872 128 Restriction1312_1_checked index (by omega) (by omega)
  else
    if cut : index < 672128 then
      exact segment_sound _ 672000 128 Restriction1312_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 672128 128 Restriction1312_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
