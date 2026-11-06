import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1092_0_checked : (List.range' 559104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1092_1_checked : (List.range' 559232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1092_2_checked : (List.range' 559360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1092_3_checked : (List.range' 559488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1092_range (index : Nat) (lower : 559104 ≤ index) (upper : index < 559616) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 559360 then
    if cut : index < 559232 then
      exact segment_sound _ 559104 128 Restriction1092_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 559232 128 Restriction1092_1_checked index (by omega) (by omega)
  else
    if cut : index < 559488 then
      exact segment_sound _ 559360 128 Restriction1092_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 559488 128 Restriction1092_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
