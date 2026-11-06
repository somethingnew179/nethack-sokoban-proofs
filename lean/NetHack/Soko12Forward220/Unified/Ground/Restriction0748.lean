import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0748_0_checked : (List.range' 382976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0748_1_checked : (List.range' 383104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0748_2_checked : (List.range' 383232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0748_3_checked : (List.range' 383360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0748_range (index : Nat) (lower : 382976 ≤ index) (upper : index < 383488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 383232 then
    if cut : index < 383104 then
      exact segment_sound _ 382976 128 Restriction0748_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 383104 128 Restriction0748_1_checked index (by omega) (by omega)
  else
    if cut : index < 383360 then
      exact segment_sound _ 383232 128 Restriction0748_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 383360 128 Restriction0748_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
