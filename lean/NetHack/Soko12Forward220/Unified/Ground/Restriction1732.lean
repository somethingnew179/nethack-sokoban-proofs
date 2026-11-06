import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1732_0_checked : (List.range' 886784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1732_1_checked : (List.range' 886912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1732_2_checked : (List.range' 887040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1732_3_checked : (List.range' 887168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1732_range (index : Nat) (lower : 886784 ≤ index) (upper : index < 887296) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 887040 then
    if cut : index < 886912 then
      exact segment_sound _ 886784 128 Restriction1732_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 886912 128 Restriction1732_1_checked index (by omega) (by omega)
  else
    if cut : index < 887168 then
      exact segment_sound _ 887040 128 Restriction1732_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 887168 128 Restriction1732_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
