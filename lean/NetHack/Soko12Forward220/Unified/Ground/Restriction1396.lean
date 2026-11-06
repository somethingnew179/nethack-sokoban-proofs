import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1396_0_checked : (List.range' 714752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1396_1_checked : (List.range' 714880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1396_2_checked : (List.range' 715008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1396_3_checked : (List.range' 715136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1396_range (index : Nat) (lower : 714752 ≤ index) (upper : index < 715264) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 715008 then
    if cut : index < 714880 then
      exact segment_sound _ 714752 128 Restriction1396_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 714880 128 Restriction1396_1_checked index (by omega) (by omega)
  else
    if cut : index < 715136 then
      exact segment_sound _ 715008 128 Restriction1396_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 715136 128 Restriction1396_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
