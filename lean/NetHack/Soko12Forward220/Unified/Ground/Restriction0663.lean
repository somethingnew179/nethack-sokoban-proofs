import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0663_0_checked : (List.range' 339456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0663_1_checked : (List.range' 339584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0663_2_checked : (List.range' 339712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0663_3_checked : (List.range' 339840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0663_range (index : Nat) (lower : 339456 ≤ index) (upper : index < 339968) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 339712 then
    if cut : index < 339584 then
      exact segment_sound _ 339456 128 Restriction0663_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 339584 128 Restriction0663_1_checked index (by omega) (by omega)
  else
    if cut : index < 339840 then
      exact segment_sound _ 339712 128 Restriction0663_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 339840 128 Restriction0663_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
