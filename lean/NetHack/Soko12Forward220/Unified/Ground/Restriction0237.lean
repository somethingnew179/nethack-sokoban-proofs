import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0237_0_checked : (List.range' 121344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0237_1_checked : (List.range' 121472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0237_2_checked : (List.range' 121600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0237_3_checked : (List.range' 121728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0237_range (index : Nat) (lower : 121344 ≤ index) (upper : index < 121856) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 121600 then
    if cut : index < 121472 then
      exact segment_sound _ 121344 128 Restriction0237_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 121472 128 Restriction0237_1_checked index (by omega) (by omega)
  else
    if cut : index < 121728 then
      exact segment_sound _ 121600 128 Restriction0237_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 121728 128 Restriction0237_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
