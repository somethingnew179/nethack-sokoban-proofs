import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1941_0_checked : (List.range' 993792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1941_1_checked : (List.range' 993920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1941_2_checked : (List.range' 994048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1941_3_checked : (List.range' 994176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1941_range (index : Nat) (lower : 993792 ≤ index) (upper : index < 994304) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 994048 then
    if cut : index < 993920 then
      exact segment_sound _ 993792 128 Restriction1941_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 993920 128 Restriction1941_1_checked index (by omega) (by omega)
  else
    if cut : index < 994176 then
      exact segment_sound _ 994048 128 Restriction1941_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 994176 128 Restriction1941_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
