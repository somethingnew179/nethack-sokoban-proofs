import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1281_0_checked : (List.range' 655872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1281_1_checked : (List.range' 656000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1281_2_checked : (List.range' 656128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1281_3_checked : (List.range' 656256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1281_range (index : Nat) (lower : 655872 ≤ index) (upper : index < 656384) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 656128 then
    if cut : index < 656000 then
      exact segment_sound _ 655872 128 Restriction1281_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 656000 128 Restriction1281_1_checked index (by omega) (by omega)
  else
    if cut : index < 656256 then
      exact segment_sound _ 656128 128 Restriction1281_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 656256 128 Restriction1281_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
