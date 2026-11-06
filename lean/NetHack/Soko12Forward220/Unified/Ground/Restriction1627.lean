import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1627_0_checked : (List.range' 833024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1627_1_checked : (List.range' 833152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1627_2_checked : (List.range' 833280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1627_3_checked : (List.range' 833408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1627_range (index : Nat) (lower : 833024 ≤ index) (upper : index < 833536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 833280 then
    if cut : index < 833152 then
      exact segment_sound _ 833024 128 Restriction1627_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 833152 128 Restriction1627_1_checked index (by omega) (by omega)
  else
    if cut : index < 833408 then
      exact segment_sound _ 833280 128 Restriction1627_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 833408 128 Restriction1627_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
