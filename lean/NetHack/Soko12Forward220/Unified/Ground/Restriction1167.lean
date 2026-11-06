import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1167_0_checked : (List.range' 597504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1167_1_checked : (List.range' 597632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1167_2_checked : (List.range' 597760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1167_3_checked : (List.range' 597888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1167_range (index : Nat) (lower : 597504 ≤ index) (upper : index < 598016) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 597760 then
    if cut : index < 597632 then
      exact segment_sound _ 597504 128 Restriction1167_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 597632 128 Restriction1167_1_checked index (by omega) (by omega)
  else
    if cut : index < 597888 then
      exact segment_sound _ 597760 128 Restriction1167_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 597888 128 Restriction1167_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
