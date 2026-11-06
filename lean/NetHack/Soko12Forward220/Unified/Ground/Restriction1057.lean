import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1057_0_checked : (List.range' 541184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1057_1_checked : (List.range' 541312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1057_2_checked : (List.range' 541440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1057_3_checked : (List.range' 541568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1057_range (index : Nat) (lower : 541184 ≤ index) (upper : index < 541696) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 541440 then
    if cut : index < 541312 then
      exact segment_sound _ 541184 128 Restriction1057_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 541312 128 Restriction1057_1_checked index (by omega) (by omega)
  else
    if cut : index < 541568 then
      exact segment_sound _ 541440 128 Restriction1057_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 541568 128 Restriction1057_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
