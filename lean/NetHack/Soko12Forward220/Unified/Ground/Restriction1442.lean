import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1442_0_checked : (List.range' 738304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1442_1_checked : (List.range' 738432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1442_2_checked : (List.range' 738560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1442_3_checked : (List.range' 738688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1442_range (index : Nat) (lower : 738304 ≤ index) (upper : index < 738816) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 738560 then
    if cut : index < 738432 then
      exact segment_sound _ 738304 128 Restriction1442_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 738432 128 Restriction1442_1_checked index (by omega) (by omega)
  else
    if cut : index < 738688 then
      exact segment_sound _ 738560 128 Restriction1442_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 738688 128 Restriction1442_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
