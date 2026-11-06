import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1995_0_checked : (List.range' 1021440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1995_1_checked : (List.range' 1021568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1995_2_checked : (List.range' 1021696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1995_3_checked : (List.range' 1021824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1995_range (index : Nat) (lower : 1021440 ≤ index) (upper : index < 1021952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1021696 then
    if cut : index < 1021568 then
      exact segment_sound _ 1021440 128 Restriction1995_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1021568 128 Restriction1995_1_checked index (by omega) (by omega)
  else
    if cut : index < 1021824 then
      exact segment_sound _ 1021696 128 Restriction1995_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1021824 128 Restriction1995_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
