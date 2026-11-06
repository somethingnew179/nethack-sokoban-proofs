import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0864_0_checked : (List.range' 442368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0864_1_checked : (List.range' 442496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0864_2_checked : (List.range' 442624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0864_3_checked : (List.range' 442752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0864_range (index : Nat) (lower : 442368 ≤ index) (upper : index < 442880) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 442624 then
    if cut : index < 442496 then
      exact segment_sound _ 442368 128 Restriction0864_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 442496 128 Restriction0864_1_checked index (by omega) (by omega)
  else
    if cut : index < 442752 then
      exact segment_sound _ 442624 128 Restriction0864_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 442752 128 Restriction0864_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
