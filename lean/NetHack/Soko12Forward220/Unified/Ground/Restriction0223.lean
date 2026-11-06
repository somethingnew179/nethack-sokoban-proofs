import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0223_0_checked : (List.range' 114176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0223_1_checked : (List.range' 114304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0223_2_checked : (List.range' 114432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0223_3_checked : (List.range' 114560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0223_range (index : Nat) (lower : 114176 ≤ index) (upper : index < 114688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 114432 then
    if cut : index < 114304 then
      exact segment_sound _ 114176 128 Restriction0223_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 114304 128 Restriction0223_1_checked index (by omega) (by omega)
  else
    if cut : index < 114560 then
      exact segment_sound _ 114432 128 Restriction0223_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 114560 128 Restriction0223_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
