import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0708_0_checked : (List.range' 362496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0708_1_checked : (List.range' 362624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0708_2_checked : (List.range' 362752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0708_3_checked : (List.range' 362880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0708_range (index : Nat) (lower : 362496 ≤ index) (upper : index < 363008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 362752 then
    if cut : index < 362624 then
      exact segment_sound _ 362496 128 Restriction0708_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 362624 128 Restriction0708_1_checked index (by omega) (by omega)
  else
    if cut : index < 362880 then
      exact segment_sound _ 362752 128 Restriction0708_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 362880 128 Restriction0708_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
