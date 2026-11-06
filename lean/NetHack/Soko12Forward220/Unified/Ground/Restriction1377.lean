import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1377_0_checked : (List.range' 705024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1377_1_checked : (List.range' 705152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1377_2_checked : (List.range' 705280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1377_3_checked : (List.range' 705408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1377_range (index : Nat) (lower : 705024 ≤ index) (upper : index < 705536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 705280 then
    if cut : index < 705152 then
      exact segment_sound _ 705024 128 Restriction1377_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 705152 128 Restriction1377_1_checked index (by omega) (by omega)
  else
    if cut : index < 705408 then
      exact segment_sound _ 705280 128 Restriction1377_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 705408 128 Restriction1377_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
