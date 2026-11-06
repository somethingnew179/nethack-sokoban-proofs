import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1520_0_checked : (List.range' 778240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1520_1_checked : (List.range' 778368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1520_2_checked : (List.range' 778496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1520_3_checked : (List.range' 778624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1520_range (index : Nat) (lower : 778240 ≤ index) (upper : index < 778752) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 778496 then
    if cut : index < 778368 then
      exact segment_sound _ 778240 128 Restriction1520_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 778368 128 Restriction1520_1_checked index (by omega) (by omega)
  else
    if cut : index < 778624 then
      exact segment_sound _ 778496 128 Restriction1520_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 778624 128 Restriction1520_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
