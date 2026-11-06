import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0633_0_checked : (List.range' 324096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0633_1_checked : (List.range' 324224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0633_2_checked : (List.range' 324352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0633_3_checked : (List.range' 324480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0633_range (index : Nat) (lower : 324096 ≤ index) (upper : index < 324608) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 324352 then
    if cut : index < 324224 then
      exact segment_sound _ 324096 128 Restriction0633_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 324224 128 Restriction0633_1_checked index (by omega) (by omega)
  else
    if cut : index < 324480 then
      exact segment_sound _ 324352 128 Restriction0633_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 324480 128 Restriction0633_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
