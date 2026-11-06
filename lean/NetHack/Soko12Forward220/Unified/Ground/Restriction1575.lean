import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1575_0_checked : (List.range' 806400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1575_1_checked : (List.range' 806528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1575_2_checked : (List.range' 806656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1575_3_checked : (List.range' 806784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1575_range (index : Nat) (lower : 806400 ≤ index) (upper : index < 806912) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 806656 then
    if cut : index < 806528 then
      exact segment_sound _ 806400 128 Restriction1575_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 806528 128 Restriction1575_1_checked index (by omega) (by omega)
  else
    if cut : index < 806784 then
      exact segment_sound _ 806656 128 Restriction1575_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 806784 128 Restriction1575_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
