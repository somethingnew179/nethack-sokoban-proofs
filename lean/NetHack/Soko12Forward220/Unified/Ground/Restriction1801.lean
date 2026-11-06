import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1801_0_checked : (List.range' 922112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1801_1_checked : (List.range' 922240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1801_2_checked : (List.range' 922368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1801_3_checked : (List.range' 922496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1801_range (index : Nat) (lower : 922112 ≤ index) (upper : index < 922624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 922368 then
    if cut : index < 922240 then
      exact segment_sound _ 922112 128 Restriction1801_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 922240 128 Restriction1801_1_checked index (by omega) (by omega)
  else
    if cut : index < 922496 then
      exact segment_sound _ 922368 128 Restriction1801_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 922496 128 Restriction1801_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
