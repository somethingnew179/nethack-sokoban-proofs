import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0066_0_checked : (List.range' 33792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0066_1_checked : (List.range' 33920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0066_2_checked : (List.range' 34048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0066_3_checked : (List.range' 34176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0066_range (index : Nat) (lower : 33792 ≤ index) (upper : index < 34304) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 34048 then
    if cut : index < 33920 then
      exact segment_sound _ 33792 128 Restriction0066_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 33920 128 Restriction0066_1_checked index (by omega) (by omega)
  else
    if cut : index < 34176 then
      exact segment_sound _ 34048 128 Restriction0066_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 34176 128 Restriction0066_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
