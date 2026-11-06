import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0715_0_checked : (List.range' 366080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0715_1_checked : (List.range' 366208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0715_2_checked : (List.range' 366336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0715_3_checked : (List.range' 366464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0715_range (index : Nat) (lower : 366080 ≤ index) (upper : index < 366592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 366336 then
    if cut : index < 366208 then
      exact segment_sound _ 366080 128 Restriction0715_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 366208 128 Restriction0715_1_checked index (by omega) (by omega)
  else
    if cut : index < 366464 then
      exact segment_sound _ 366336 128 Restriction0715_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 366464 128 Restriction0715_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
