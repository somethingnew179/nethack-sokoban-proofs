import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0972_0_checked : (List.range' 497664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0972_1_checked : (List.range' 497792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0972_2_checked : (List.range' 497920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0972_3_checked : (List.range' 498048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0972_range (index : Nat) (lower : 497664 ≤ index) (upper : index < 498176) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 497920 then
    if cut : index < 497792 then
      exact segment_sound _ 497664 128 Restriction0972_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 497792 128 Restriction0972_1_checked index (by omega) (by omega)
  else
    if cut : index < 498048 then
      exact segment_sound _ 497920 128 Restriction0972_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 498048 128 Restriction0972_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
