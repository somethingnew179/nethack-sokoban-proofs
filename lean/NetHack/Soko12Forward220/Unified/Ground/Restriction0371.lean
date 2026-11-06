import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0371_0_checked : (List.range' 189952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0371_1_checked : (List.range' 190080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0371_2_checked : (List.range' 190208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0371_3_checked : (List.range' 190336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0371_range (index : Nat) (lower : 189952 ≤ index) (upper : index < 190464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 190208 then
    if cut : index < 190080 then
      exact segment_sound _ 189952 128 Restriction0371_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 190080 128 Restriction0371_1_checked index (by omega) (by omega)
  else
    if cut : index < 190336 then
      exact segment_sound _ 190208 128 Restriction0371_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 190336 128 Restriction0371_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
