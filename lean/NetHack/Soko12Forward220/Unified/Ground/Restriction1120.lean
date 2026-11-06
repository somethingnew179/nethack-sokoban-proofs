import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1120_0_checked : (List.range' 573440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1120_1_checked : (List.range' 573568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1120_2_checked : (List.range' 573696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1120_3_checked : (List.range' 573824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1120_range (index : Nat) (lower : 573440 ≤ index) (upper : index < 573952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 573696 then
    if cut : index < 573568 then
      exact segment_sound _ 573440 128 Restriction1120_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 573568 128 Restriction1120_1_checked index (by omega) (by omega)
  else
    if cut : index < 573824 then
      exact segment_sound _ 573696 128 Restriction1120_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 573824 128 Restriction1120_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
