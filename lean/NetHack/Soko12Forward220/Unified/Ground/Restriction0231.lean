import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0231_0_checked : (List.range' 118272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0231_1_checked : (List.range' 118400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0231_2_checked : (List.range' 118528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0231_3_checked : (List.range' 118656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0231_range (index : Nat) (lower : 118272 ≤ index) (upper : index < 118784) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 118528 then
    if cut : index < 118400 then
      exact segment_sound _ 118272 128 Restriction0231_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 118400 128 Restriction0231_1_checked index (by omega) (by omega)
  else
    if cut : index < 118656 then
      exact segment_sound _ 118528 128 Restriction0231_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 118656 128 Restriction0231_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
