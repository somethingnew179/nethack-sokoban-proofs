import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1907_0_checked : (List.range' 976384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1907_1_checked : (List.range' 976512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1907_2_checked : (List.range' 976640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1907_3_checked : (List.range' 976768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1907_range (index : Nat) (lower : 976384 ≤ index) (upper : index < 976896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 976640 then
    if cut : index < 976512 then
      exact segment_sound _ 976384 128 Restriction1907_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 976512 128 Restriction1907_1_checked index (by omega) (by omega)
  else
    if cut : index < 976768 then
      exact segment_sound _ 976640 128 Restriction1907_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 976768 128 Restriction1907_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
