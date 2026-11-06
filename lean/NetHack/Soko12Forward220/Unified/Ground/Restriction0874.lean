import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0874_0_checked : (List.range' 447488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0874_1_checked : (List.range' 447616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0874_2_checked : (List.range' 447744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0874_3_checked : (List.range' 447872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0874_range (index : Nat) (lower : 447488 ≤ index) (upper : index < 448000) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 447744 then
    if cut : index < 447616 then
      exact segment_sound _ 447488 128 Restriction0874_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 447616 128 Restriction0874_1_checked index (by omega) (by omega)
  else
    if cut : index < 447872 then
      exact segment_sound _ 447744 128 Restriction0874_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 447872 128 Restriction0874_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
