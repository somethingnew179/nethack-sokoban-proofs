import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1623_0_checked : (List.range' 830976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1623_1_checked : (List.range' 831104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1623_2_checked : (List.range' 831232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1623_3_checked : (List.range' 831360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1623_range (index : Nat) (lower : 830976 ≤ index) (upper : index < 831488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 831232 then
    if cut : index < 831104 then
      exact segment_sound _ 830976 128 Restriction1623_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 831104 128 Restriction1623_1_checked index (by omega) (by omega)
  else
    if cut : index < 831360 then
      exact segment_sound _ 831232 128 Restriction1623_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 831360 128 Restriction1623_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
