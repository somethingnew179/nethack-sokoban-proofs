import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1987_0_checked : (List.range' 1017344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1987_1_checked : (List.range' 1017472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1987_2_checked : (List.range' 1017600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1987_3_checked : (List.range' 1017728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1987_range (index : Nat) (lower : 1017344 ≤ index) (upper : index < 1017856) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1017600 then
    if cut : index < 1017472 then
      exact segment_sound _ 1017344 128 Restriction1987_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1017472 128 Restriction1987_1_checked index (by omega) (by omega)
  else
    if cut : index < 1017728 then
      exact segment_sound _ 1017600 128 Restriction1987_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1017728 128 Restriction1987_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
