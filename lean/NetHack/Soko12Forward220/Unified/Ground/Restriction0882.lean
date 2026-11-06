import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0882_0_checked : (List.range' 451584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0882_1_checked : (List.range' 451712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0882_2_checked : (List.range' 451840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0882_3_checked : (List.range' 451968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0882_range (index : Nat) (lower : 451584 ≤ index) (upper : index < 452096) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 451840 then
    if cut : index < 451712 then
      exact segment_sound _ 451584 128 Restriction0882_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 451712 128 Restriction0882_1_checked index (by omega) (by omega)
  else
    if cut : index < 451968 then
      exact segment_sound _ 451840 128 Restriction0882_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 451968 128 Restriction0882_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
