import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1473_0_checked : (List.range' 754176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1473_1_checked : (List.range' 754304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1473_2_checked : (List.range' 754432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1473_3_checked : (List.range' 754560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1473_range (index : Nat) (lower : 754176 ≤ index) (upper : index < 754688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 754432 then
    if cut : index < 754304 then
      exact segment_sound _ 754176 128 Restriction1473_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 754304 128 Restriction1473_1_checked index (by omega) (by omega)
  else
    if cut : index < 754560 then
      exact segment_sound _ 754432 128 Restriction1473_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 754560 128 Restriction1473_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
