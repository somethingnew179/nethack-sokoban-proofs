import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0303_0_checked : (List.range' 155136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0303_1_checked : (List.range' 155264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0303_2_checked : (List.range' 155392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0303_3_checked : (List.range' 155520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0303_range (index : Nat) (lower : 155136 ≤ index) (upper : index < 155648) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 155392 then
    if cut : index < 155264 then
      exact segment_sound _ 155136 128 Restriction0303_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 155264 128 Restriction0303_1_checked index (by omega) (by omega)
  else
    if cut : index < 155520 then
      exact segment_sound _ 155392 128 Restriction0303_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 155520 128 Restriction0303_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
