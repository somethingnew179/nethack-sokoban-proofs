import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0877_0_checked : (List.range' 449024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0877_1_checked : (List.range' 449152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0877_2_checked : (List.range' 449280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0877_3_checked : (List.range' 449408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0877_range (index : Nat) (lower : 449024 ≤ index) (upper : index < 449536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 449280 then
    if cut : index < 449152 then
      exact segment_sound _ 449024 128 Restriction0877_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 449152 128 Restriction0877_1_checked index (by omega) (by omega)
  else
    if cut : index < 449408 then
      exact segment_sound _ 449280 128 Restriction0877_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 449408 128 Restriction0877_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
