import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0746_0_checked : (List.range' 381952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0746_1_checked : (List.range' 382080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0746_2_checked : (List.range' 382208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0746_3_checked : (List.range' 382336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0746_range (index : Nat) (lower : 381952 ≤ index) (upper : index < 382464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 382208 then
    if cut : index < 382080 then
      exact segment_sound _ 381952 128 Restriction0746_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 382080 128 Restriction0746_1_checked index (by omega) (by omega)
  else
    if cut : index < 382336 then
      exact segment_sound _ 382208 128 Restriction0746_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 382336 128 Restriction0746_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
