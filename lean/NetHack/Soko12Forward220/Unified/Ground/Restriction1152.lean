import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1152_0_checked : (List.range' 589824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1152_1_checked : (List.range' 589952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1152_2_checked : (List.range' 590080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1152_3_checked : (List.range' 590208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1152_range (index : Nat) (lower : 589824 ≤ index) (upper : index < 590336) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 590080 then
    if cut : index < 589952 then
      exact segment_sound _ 589824 128 Restriction1152_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 589952 128 Restriction1152_1_checked index (by omega) (by omega)
  else
    if cut : index < 590208 then
      exact segment_sound _ 590080 128 Restriction1152_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 590208 128 Restriction1152_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
