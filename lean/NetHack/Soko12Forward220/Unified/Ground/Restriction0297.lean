import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0297_0_checked : (List.range' 152064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0297_1_checked : (List.range' 152192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0297_2_checked : (List.range' 152320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0297_3_checked : (List.range' 152448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0297_range (index : Nat) (lower : 152064 ≤ index) (upper : index < 152576) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 152320 then
    if cut : index < 152192 then
      exact segment_sound _ 152064 128 Restriction0297_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 152192 128 Restriction0297_1_checked index (by omega) (by omega)
  else
    if cut : index < 152448 then
      exact segment_sound _ 152320 128 Restriction0297_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 152448 128 Restriction0297_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
