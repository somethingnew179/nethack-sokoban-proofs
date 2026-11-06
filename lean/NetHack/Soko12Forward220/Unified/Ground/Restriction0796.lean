import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0796_0_checked : (List.range' 407552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0796_1_checked : (List.range' 407680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0796_2_checked : (List.range' 407808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0796_3_checked : (List.range' 407936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0796_range (index : Nat) (lower : 407552 ≤ index) (upper : index < 408064) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 407808 then
    if cut : index < 407680 then
      exact segment_sound _ 407552 128 Restriction0796_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 407680 128 Restriction0796_1_checked index (by omega) (by omega)
  else
    if cut : index < 407936 then
      exact segment_sound _ 407808 128 Restriction0796_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 407936 128 Restriction0796_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
