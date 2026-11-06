import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1672_0_checked : (List.range' 856064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1672_1_checked : (List.range' 856192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1672_2_checked : (List.range' 856320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1672_3_checked : (List.range' 856448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1672_range (index : Nat) (lower : 856064 ≤ index) (upper : index < 856576) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 856320 then
    if cut : index < 856192 then
      exact segment_sound _ 856064 128 Restriction1672_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 856192 128 Restriction1672_1_checked index (by omega) (by omega)
  else
    if cut : index < 856448 then
      exact segment_sound _ 856320 128 Restriction1672_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 856448 128 Restriction1672_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
