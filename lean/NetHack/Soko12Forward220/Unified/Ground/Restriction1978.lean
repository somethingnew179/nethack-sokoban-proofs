import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1978_0_checked : (List.range' 1012736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1978_1_checked : (List.range' 1012864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1978_2_checked : (List.range' 1012992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1978_3_checked : (List.range' 1013120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1978_range (index : Nat) (lower : 1012736 ≤ index) (upper : index < 1013248) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1012992 then
    if cut : index < 1012864 then
      exact segment_sound _ 1012736 128 Restriction1978_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1012864 128 Restriction1978_1_checked index (by omega) (by omega)
  else
    if cut : index < 1013120 then
      exact segment_sound _ 1012992 128 Restriction1978_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1013120 128 Restriction1978_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
