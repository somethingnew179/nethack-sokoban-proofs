import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0959_0_checked : (List.range' 491008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0959_1_checked : (List.range' 491136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0959_2_checked : (List.range' 491264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0959_3_checked : (List.range' 491392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0959_range (index : Nat) (lower : 491008 ≤ index) (upper : index < 491520) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 491264 then
    if cut : index < 491136 then
      exact segment_sound _ 491008 128 Restriction0959_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 491136 128 Restriction0959_1_checked index (by omega) (by omega)
  else
    if cut : index < 491392 then
      exact segment_sound _ 491264 128 Restriction0959_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 491392 128 Restriction0959_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
