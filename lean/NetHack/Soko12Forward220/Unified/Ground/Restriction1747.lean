import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1747_0_checked : (List.range' 894464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1747_1_checked : (List.range' 894592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1747_2_checked : (List.range' 894720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1747_3_checked : (List.range' 894848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1747_range (index : Nat) (lower : 894464 ≤ index) (upper : index < 894976) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 894720 then
    if cut : index < 894592 then
      exact segment_sound _ 894464 128 Restriction1747_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 894592 128 Restriction1747_1_checked index (by omega) (by omega)
  else
    if cut : index < 894848 then
      exact segment_sound _ 894720 128 Restriction1747_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 894848 128 Restriction1747_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
