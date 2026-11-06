import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0944_0_checked : (List.range' 483328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0944_1_checked : (List.range' 483456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0944_2_checked : (List.range' 483584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0944_3_checked : (List.range' 483712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0944_range (index : Nat) (lower : 483328 ≤ index) (upper : index < 483840) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 483584 then
    if cut : index < 483456 then
      exact segment_sound _ 483328 128 Restriction0944_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 483456 128 Restriction0944_1_checked index (by omega) (by omega)
  else
    if cut : index < 483712 then
      exact segment_sound _ 483584 128 Restriction0944_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 483712 128 Restriction0944_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
