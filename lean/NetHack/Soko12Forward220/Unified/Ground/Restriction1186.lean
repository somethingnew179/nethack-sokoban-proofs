import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1186_0_checked : (List.range' 607232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1186_1_checked : (List.range' 607360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1186_2_checked : (List.range' 607488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1186_3_checked : (List.range' 607616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1186_range (index : Nat) (lower : 607232 ≤ index) (upper : index < 607744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 607488 then
    if cut : index < 607360 then
      exact segment_sound _ 607232 128 Restriction1186_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 607360 128 Restriction1186_1_checked index (by omega) (by omega)
  else
    if cut : index < 607616 then
      exact segment_sound _ 607488 128 Restriction1186_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 607616 128 Restriction1186_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
