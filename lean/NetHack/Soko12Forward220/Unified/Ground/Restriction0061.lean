import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0061_0_checked : (List.range' 31232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0061_1_checked : (List.range' 31360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0061_2_checked : (List.range' 31488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0061_3_checked : (List.range' 31616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0061_range (index : Nat) (lower : 31232 ≤ index) (upper : index < 31744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 31488 then
    if cut : index < 31360 then
      exact segment_sound _ 31232 128 Restriction0061_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 31360 128 Restriction0061_1_checked index (by omega) (by omega)
  else
    if cut : index < 31616 then
      exact segment_sound _ 31488 128 Restriction0061_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 31616 128 Restriction0061_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
