import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1132_0_checked : (List.range' 579584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1132_1_checked : (List.range' 579712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1132_2_checked : (List.range' 579840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1132_3_checked : (List.range' 579968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1132_range (index : Nat) (lower : 579584 ≤ index) (upper : index < 580096) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 579840 then
    if cut : index < 579712 then
      exact segment_sound _ 579584 128 Restriction1132_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 579712 128 Restriction1132_1_checked index (by omega) (by omega)
  else
    if cut : index < 579968 then
      exact segment_sound _ 579840 128 Restriction1132_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 579968 128 Restriction1132_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
