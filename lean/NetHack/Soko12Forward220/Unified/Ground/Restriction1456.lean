import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1456_0_checked : (List.range' 745472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1456_1_checked : (List.range' 745600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1456_2_checked : (List.range' 745728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1456_3_checked : (List.range' 745856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1456_range (index : Nat) (lower : 745472 ≤ index) (upper : index < 745984) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 745728 then
    if cut : index < 745600 then
      exact segment_sound _ 745472 128 Restriction1456_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 745600 128 Restriction1456_1_checked index (by omega) (by omega)
  else
    if cut : index < 745856 then
      exact segment_sound _ 745728 128 Restriction1456_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 745856 128 Restriction1456_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
