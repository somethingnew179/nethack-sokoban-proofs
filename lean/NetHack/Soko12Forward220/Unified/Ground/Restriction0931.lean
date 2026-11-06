import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0931_0_checked : (List.range' 476672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0931_1_checked : (List.range' 476800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0931_2_checked : (List.range' 476928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0931_3_checked : (List.range' 477056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0931_range (index : Nat) (lower : 476672 ≤ index) (upper : index < 477184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 476928 then
    if cut : index < 476800 then
      exact segment_sound _ 476672 128 Restriction0931_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 476800 128 Restriction0931_1_checked index (by omega) (by omega)
  else
    if cut : index < 477056 then
      exact segment_sound _ 476928 128 Restriction0931_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 477056 128 Restriction0931_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
