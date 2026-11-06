import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0819_0_checked : (List.range' 419328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0819_1_checked : (List.range' 419456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0819_2_checked : (List.range' 419584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0819_3_checked : (List.range' 419712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0819_range (index : Nat) (lower : 419328 ≤ index) (upper : index < 419840) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 419584 then
    if cut : index < 419456 then
      exact segment_sound _ 419328 128 Restriction0819_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 419456 128 Restriction0819_1_checked index (by omega) (by omega)
  else
    if cut : index < 419712 then
      exact segment_sound _ 419584 128 Restriction0819_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 419712 128 Restriction0819_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
