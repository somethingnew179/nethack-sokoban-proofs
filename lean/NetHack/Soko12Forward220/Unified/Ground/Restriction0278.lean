import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0278_0_checked : (List.range' 142336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0278_1_checked : (List.range' 142464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0278_2_checked : (List.range' 142592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0278_3_checked : (List.range' 142720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0278_range (index : Nat) (lower : 142336 ≤ index) (upper : index < 142848) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 142592 then
    if cut : index < 142464 then
      exact segment_sound _ 142336 128 Restriction0278_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 142464 128 Restriction0278_1_checked index (by omega) (by omega)
  else
    if cut : index < 142720 then
      exact segment_sound _ 142592 128 Restriction0278_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 142720 128 Restriction0278_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
