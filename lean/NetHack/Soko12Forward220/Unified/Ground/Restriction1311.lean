import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1311_0_checked : (List.range' 671232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1311_1_checked : (List.range' 671360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1311_2_checked : (List.range' 671488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1311_3_checked : (List.range' 671616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1311_range (index : Nat) (lower : 671232 ≤ index) (upper : index < 671744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 671488 then
    if cut : index < 671360 then
      exact segment_sound _ 671232 128 Restriction1311_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 671360 128 Restriction1311_1_checked index (by omega) (by omega)
  else
    if cut : index < 671616 then
      exact segment_sound _ 671488 128 Restriction1311_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 671616 128 Restriction1311_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
