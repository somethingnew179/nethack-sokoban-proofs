import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1503_0_checked : (List.range' 769536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1503_1_checked : (List.range' 769664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1503_2_checked : (List.range' 769792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1503_3_checked : (List.range' 769920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1503_range (index : Nat) (lower : 769536 ≤ index) (upper : index < 770048) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 769792 then
    if cut : index < 769664 then
      exact segment_sound _ 769536 128 Restriction1503_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 769664 128 Restriction1503_1_checked index (by omega) (by omega)
  else
    if cut : index < 769920 then
      exact segment_sound _ 769792 128 Restriction1503_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 769920 128 Restriction1503_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
