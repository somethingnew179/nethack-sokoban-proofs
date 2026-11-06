import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1089_0_checked : (List.range' 557568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1089_1_checked : (List.range' 557696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1089_2_checked : (List.range' 557824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1089_3_checked : (List.range' 557952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1089_range (index : Nat) (lower : 557568 ≤ index) (upper : index < 558080) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 557824 then
    if cut : index < 557696 then
      exact segment_sound _ 557568 128 Restriction1089_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 557696 128 Restriction1089_1_checked index (by omega) (by omega)
  else
    if cut : index < 557952 then
      exact segment_sound _ 557824 128 Restriction1089_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 557952 128 Restriction1089_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
