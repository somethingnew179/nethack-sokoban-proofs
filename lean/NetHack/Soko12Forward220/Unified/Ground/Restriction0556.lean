import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0556_0_checked : (List.range' 284672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0556_1_checked : (List.range' 284800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0556_2_checked : (List.range' 284928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0556_3_checked : (List.range' 285056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0556_range (index : Nat) (lower : 284672 ≤ index) (upper : index < 285184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 284928 then
    if cut : index < 284800 then
      exact segment_sound _ 284672 128 Restriction0556_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 284800 128 Restriction0556_1_checked index (by omega) (by omega)
  else
    if cut : index < 285056 then
      exact segment_sound _ 284928 128 Restriction0556_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 285056 128 Restriction0556_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
