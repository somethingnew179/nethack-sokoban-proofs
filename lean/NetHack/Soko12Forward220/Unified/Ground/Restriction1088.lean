import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1088_0_checked : (List.range' 557056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1088_1_checked : (List.range' 557184 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1088_2_checked : (List.range' 557312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1088_3_checked : (List.range' 557440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1088_range (index : Nat) (lower : 557056 ≤ index) (upper : index < 557568) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 557312 then
    if cut : index < 557184 then
      exact segment_sound _ 557056 128 Restriction1088_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 557184 128 Restriction1088_1_checked index (by omega) (by omega)
  else
    if cut : index < 557440 then
      exact segment_sound _ 557312 128 Restriction1088_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 557440 128 Restriction1088_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
