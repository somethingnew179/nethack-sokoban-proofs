import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1070_0_checked : (List.range' 547840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1070_1_checked : (List.range' 547968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1070_2_checked : (List.range' 548096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1070_3_checked : (List.range' 548224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1070_range (index : Nat) (lower : 547840 ≤ index) (upper : index < 548352) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 548096 then
    if cut : index < 547968 then
      exact segment_sound _ 547840 128 Restriction1070_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 547968 128 Restriction1070_1_checked index (by omega) (by omega)
  else
    if cut : index < 548224 then
      exact segment_sound _ 548096 128 Restriction1070_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 548224 128 Restriction1070_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
