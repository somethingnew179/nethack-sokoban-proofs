import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1319_0_checked : (List.range' 675328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1319_1_checked : (List.range' 675456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1319_2_checked : (List.range' 675584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1319_3_checked : (List.range' 675712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1319_range (index : Nat) (lower : 675328 ≤ index) (upper : index < 675840) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 675584 then
    if cut : index < 675456 then
      exact segment_sound _ 675328 128 Restriction1319_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 675456 128 Restriction1319_1_checked index (by omega) (by omega)
  else
    if cut : index < 675712 then
      exact segment_sound _ 675584 128 Restriction1319_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 675712 128 Restriction1319_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
