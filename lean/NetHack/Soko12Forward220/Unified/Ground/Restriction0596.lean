import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0596_0_checked : (List.range' 305152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0596_1_checked : (List.range' 305280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0596_2_checked : (List.range' 305408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0596_3_checked : (List.range' 305536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0596_range (index : Nat) (lower : 305152 ≤ index) (upper : index < 305664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 305408 then
    if cut : index < 305280 then
      exact segment_sound _ 305152 128 Restriction0596_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 305280 128 Restriction0596_1_checked index (by omega) (by omega)
  else
    if cut : index < 305536 then
      exact segment_sound _ 305408 128 Restriction0596_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 305536 128 Restriction0596_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
