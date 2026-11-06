import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1746_0_checked : (List.range' 893952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1746_1_checked : (List.range' 894080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1746_2_checked : (List.range' 894208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1746_3_checked : (List.range' 894336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1746_range (index : Nat) (lower : 893952 ≤ index) (upper : index < 894464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 894208 then
    if cut : index < 894080 then
      exact segment_sound _ 893952 128 Restriction1746_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 894080 128 Restriction1746_1_checked index (by omega) (by omega)
  else
    if cut : index < 894336 then
      exact segment_sound _ 894208 128 Restriction1746_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 894336 128 Restriction1746_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
