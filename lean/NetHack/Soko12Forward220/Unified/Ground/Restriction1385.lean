import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1385_0_checked : (List.range' 709120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1385_1_checked : (List.range' 709248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1385_2_checked : (List.range' 709376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1385_3_checked : (List.range' 709504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1385_range (index : Nat) (lower : 709120 ≤ index) (upper : index < 709632) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 709376 then
    if cut : index < 709248 then
      exact segment_sound _ 709120 128 Restriction1385_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 709248 128 Restriction1385_1_checked index (by omega) (by omega)
  else
    if cut : index < 709504 then
      exact segment_sound _ 709376 128 Restriction1385_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 709504 128 Restriction1385_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
