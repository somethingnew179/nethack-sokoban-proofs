import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1095_0_checked : (List.range' 560640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1095_1_checked : (List.range' 560768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1095_2_checked : (List.range' 560896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1095_3_checked : (List.range' 561024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1095_range (index : Nat) (lower : 560640 ≤ index) (upper : index < 561152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 560896 then
    if cut : index < 560768 then
      exact segment_sound _ 560640 128 Restriction1095_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 560768 128 Restriction1095_1_checked index (by omega) (by omega)
  else
    if cut : index < 561024 then
      exact segment_sound _ 560896 128 Restriction1095_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 561024 128 Restriction1095_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
