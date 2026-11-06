import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1380_0_checked : (List.range' 706560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1380_1_checked : (List.range' 706688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1380_2_checked : (List.range' 706816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1380_3_checked : (List.range' 706944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1380_range (index : Nat) (lower : 706560 ≤ index) (upper : index < 707072) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 706816 then
    if cut : index < 706688 then
      exact segment_sound _ 706560 128 Restriction1380_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 706688 128 Restriction1380_1_checked index (by omega) (by omega)
  else
    if cut : index < 706944 then
      exact segment_sound _ 706816 128 Restriction1380_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 706944 128 Restriction1380_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
