import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0101_0_checked : (List.range' 51712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0101_1_checked : (List.range' 51840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0101_2_checked : (List.range' 51968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0101_3_checked : (List.range' 52096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0101_range (index : Nat) (lower : 51712 ≤ index) (upper : index < 52224) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 51968 then
    if cut : index < 51840 then
      exact segment_sound _ 51712 128 Restriction0101_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 51840 128 Restriction0101_1_checked index (by omega) (by omega)
  else
    if cut : index < 52096 then
      exact segment_sound _ 51968 128 Restriction0101_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 52096 128 Restriction0101_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
