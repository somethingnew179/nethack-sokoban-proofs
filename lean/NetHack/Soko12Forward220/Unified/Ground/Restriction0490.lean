import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0490_0_checked : (List.range' 250880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0490_1_checked : (List.range' 251008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0490_2_checked : (List.range' 251136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0490_3_checked : (List.range' 251264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0490_range (index : Nat) (lower : 250880 ≤ index) (upper : index < 251392) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 251136 then
    if cut : index < 251008 then
      exact segment_sound _ 250880 128 Restriction0490_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 251008 128 Restriction0490_1_checked index (by omega) (by omega)
  else
    if cut : index < 251264 then
      exact segment_sound _ 251136 128 Restriction0490_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 251264 128 Restriction0490_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
