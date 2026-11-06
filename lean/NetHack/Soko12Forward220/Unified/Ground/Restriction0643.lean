import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0643_0_checked : (List.range' 329216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0643_1_checked : (List.range' 329344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0643_2_checked : (List.range' 329472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0643_3_checked : (List.range' 329600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0643_range (index : Nat) (lower : 329216 ≤ index) (upper : index < 329728) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 329472 then
    if cut : index < 329344 then
      exact segment_sound _ 329216 128 Restriction0643_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 329344 128 Restriction0643_1_checked index (by omega) (by omega)
  else
    if cut : index < 329600 then
      exact segment_sound _ 329472 128 Restriction0643_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 329600 128 Restriction0643_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
