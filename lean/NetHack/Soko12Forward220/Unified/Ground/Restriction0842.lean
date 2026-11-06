import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0842_0_checked : (List.range' 431104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0842_1_checked : (List.range' 431232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0842_2_checked : (List.range' 431360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0842_3_checked : (List.range' 431488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0842_range (index : Nat) (lower : 431104 ≤ index) (upper : index < 431616) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 431360 then
    if cut : index < 431232 then
      exact segment_sound _ 431104 128 Restriction0842_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 431232 128 Restriction0842_1_checked index (by omega) (by omega)
  else
    if cut : index < 431488 then
      exact segment_sound _ 431360 128 Restriction0842_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 431488 128 Restriction0842_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
