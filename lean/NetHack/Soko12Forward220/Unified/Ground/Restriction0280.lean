import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0280_0_checked : (List.range' 143360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0280_1_checked : (List.range' 143488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0280_2_checked : (List.range' 143616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0280_3_checked : (List.range' 143744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0280_range (index : Nat) (lower : 143360 ≤ index) (upper : index < 143872) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 143616 then
    if cut : index < 143488 then
      exact segment_sound _ 143360 128 Restriction0280_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 143488 128 Restriction0280_1_checked index (by omega) (by omega)
  else
    if cut : index < 143744 then
      exact segment_sound _ 143616 128 Restriction0280_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 143744 128 Restriction0280_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
