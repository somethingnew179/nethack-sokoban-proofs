import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0817_0_checked : (List.range' 418304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0817_1_checked : (List.range' 418432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0817_2_checked : (List.range' 418560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0817_3_checked : (List.range' 418688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0817_range (index : Nat) (lower : 418304 ≤ index) (upper : index < 418816) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 418560 then
    if cut : index < 418432 then
      exact segment_sound _ 418304 128 Restriction0817_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 418432 128 Restriction0817_1_checked index (by omega) (by omega)
  else
    if cut : index < 418688 then
      exact segment_sound _ 418560 128 Restriction0817_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 418688 128 Restriction0817_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
