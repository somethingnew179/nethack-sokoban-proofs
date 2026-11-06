import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1553_0_checked : (List.range' 795136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1553_1_checked : (List.range' 795264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1553_2_checked : (List.range' 795392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1553_3_checked : (List.range' 795520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1553_range (index : Nat) (lower : 795136 ≤ index) (upper : index < 795648) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 795392 then
    if cut : index < 795264 then
      exact segment_sound _ 795136 128 Restriction1553_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 795264 128 Restriction1553_1_checked index (by omega) (by omega)
  else
    if cut : index < 795520 then
      exact segment_sound _ 795392 128 Restriction1553_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 795520 128 Restriction1553_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
