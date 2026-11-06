import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0686_0_checked : (List.range' 351232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0686_1_checked : (List.range' 351360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0686_2_checked : (List.range' 351488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0686_3_checked : (List.range' 351616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0686_range (index : Nat) (lower : 351232 ≤ index) (upper : index < 351744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 351488 then
    if cut : index < 351360 then
      exact segment_sound _ 351232 128 Restriction0686_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 351360 128 Restriction0686_1_checked index (by omega) (by omega)
  else
    if cut : index < 351616 then
      exact segment_sound _ 351488 128 Restriction0686_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 351616 128 Restriction0686_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
