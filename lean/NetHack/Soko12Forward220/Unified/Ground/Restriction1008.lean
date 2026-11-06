import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1008_0_checked : (List.range' 516096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1008_1_checked : (List.range' 516224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1008_2_checked : (List.range' 516352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1008_3_checked : (List.range' 516480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1008_range (index : Nat) (lower : 516096 ≤ index) (upper : index < 516608) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 516352 then
    if cut : index < 516224 then
      exact segment_sound _ 516096 128 Restriction1008_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 516224 128 Restriction1008_1_checked index (by omega) (by omega)
  else
    if cut : index < 516480 then
      exact segment_sound _ 516352 128 Restriction1008_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 516480 128 Restriction1008_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
