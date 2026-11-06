import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1534_0_checked : (List.range' 785408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1534_1_checked : (List.range' 785536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1534_2_checked : (List.range' 785664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1534_3_checked : (List.range' 785792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1534_range (index : Nat) (lower : 785408 ≤ index) (upper : index < 785920) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 785664 then
    if cut : index < 785536 then
      exact segment_sound _ 785408 128 Restriction1534_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 785536 128 Restriction1534_1_checked index (by omega) (by omega)
  else
    if cut : index < 785792 then
      exact segment_sound _ 785664 128 Restriction1534_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 785792 128 Restriction1534_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
