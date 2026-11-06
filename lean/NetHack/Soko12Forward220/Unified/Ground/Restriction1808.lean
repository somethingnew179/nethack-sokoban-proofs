import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1808_0_checked : (List.range' 925696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1808_1_checked : (List.range' 925824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1808_2_checked : (List.range' 925952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1808_3_checked : (List.range' 926080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1808_range (index : Nat) (lower : 925696 ≤ index) (upper : index < 926208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 925952 then
    if cut : index < 925824 then
      exact segment_sound _ 925696 128 Restriction1808_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 925824 128 Restriction1808_1_checked index (by omega) (by omega)
  else
    if cut : index < 926080 then
      exact segment_sound _ 925952 128 Restriction1808_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 926080 128 Restriction1808_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
