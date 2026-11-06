import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0928_0_checked : (List.range' 475136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0928_1_checked : (List.range' 475264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0928_2_checked : (List.range' 475392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0928_3_checked : (List.range' 475520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0928_range (index : Nat) (lower : 475136 ≤ index) (upper : index < 475648) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 475392 then
    if cut : index < 475264 then
      exact segment_sound _ 475136 128 Restriction0928_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 475264 128 Restriction0928_1_checked index (by omega) (by omega)
  else
    if cut : index < 475520 then
      exact segment_sound _ 475392 128 Restriction0928_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 475520 128 Restriction0928_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
