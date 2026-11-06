import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0851_0_checked : (List.range' 435712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0851_1_checked : (List.range' 435840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0851_2_checked : (List.range' 435968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0851_3_checked : (List.range' 436096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0851_range (index : Nat) (lower : 435712 ≤ index) (upper : index < 436224) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 435968 then
    if cut : index < 435840 then
      exact segment_sound _ 435712 128 Restriction0851_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 435840 128 Restriction0851_1_checked index (by omega) (by omega)
  else
    if cut : index < 436096 then
      exact segment_sound _ 435968 128 Restriction0851_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 436096 128 Restriction0851_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
