import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0781_0_checked : (List.range' 399872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0781_1_checked : (List.range' 400000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0781_2_checked : (List.range' 400128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0781_3_checked : (List.range' 400256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0781_range (index : Nat) (lower : 399872 ≤ index) (upper : index < 400384) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 400128 then
    if cut : index < 400000 then
      exact segment_sound _ 399872 128 Restriction0781_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 400000 128 Restriction0781_1_checked index (by omega) (by omega)
  else
    if cut : index < 400256 then
      exact segment_sound _ 400128 128 Restriction0781_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 400256 128 Restriction0781_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
