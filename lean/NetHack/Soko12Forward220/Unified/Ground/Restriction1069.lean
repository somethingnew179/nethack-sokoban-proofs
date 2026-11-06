import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1069_0_checked : (List.range' 547328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1069_1_checked : (List.range' 547456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1069_2_checked : (List.range' 547584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1069_3_checked : (List.range' 547712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1069_range (index : Nat) (lower : 547328 ≤ index) (upper : index < 547840) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 547584 then
    if cut : index < 547456 then
      exact segment_sound _ 547328 128 Restriction1069_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 547456 128 Restriction1069_1_checked index (by omega) (by omega)
  else
    if cut : index < 547712 then
      exact segment_sound _ 547584 128 Restriction1069_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 547712 128 Restriction1069_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
