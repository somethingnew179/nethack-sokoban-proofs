import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1294_0_checked : (List.range' 662528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1294_1_checked : (List.range' 662656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1294_2_checked : (List.range' 662784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1294_3_checked : (List.range' 662912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1294_range (index : Nat) (lower : 662528 ≤ index) (upper : index < 663040) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 662784 then
    if cut : index < 662656 then
      exact segment_sound _ 662528 128 Restriction1294_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 662656 128 Restriction1294_1_checked index (by omega) (by omega)
  else
    if cut : index < 662912 then
      exact segment_sound _ 662784 128 Restriction1294_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 662912 128 Restriction1294_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
