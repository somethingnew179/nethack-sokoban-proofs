import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2624_0_checked : (List.range' 1343488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2624_1_checked : (List.range' 1343616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2624_2_checked : (List.range' 1343744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2624_3_checked : (List.range' 1343872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2624_range (index : Nat) (lower : 1343488 ≤ index) (upper : index < 1344000) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1343744 then
    if cut : index < 1343616 then
      exact segment_sound _ 1343488 128 Restriction2624_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1343616 128 Restriction2624_1_checked index (by omega) (by omega)
  else
    if cut : index < 1343872 then
      exact segment_sound _ 1343744 128 Restriction2624_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1343872 128 Restriction2624_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
