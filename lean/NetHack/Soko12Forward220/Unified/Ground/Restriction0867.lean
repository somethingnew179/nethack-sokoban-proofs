import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0867_0_checked : (List.range' 443904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0867_1_checked : (List.range' 444032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0867_2_checked : (List.range' 444160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0867_3_checked : (List.range' 444288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0867_range (index : Nat) (lower : 443904 ≤ index) (upper : index < 444416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 444160 then
    if cut : index < 444032 then
      exact segment_sound _ 443904 128 Restriction0867_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 444032 128 Restriction0867_1_checked index (by omega) (by omega)
  else
    if cut : index < 444288 then
      exact segment_sound _ 444160 128 Restriction0867_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 444288 128 Restriction0867_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
