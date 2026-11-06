import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1700_0_checked : (List.range' 870400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1700_1_checked : (List.range' 870528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1700_2_checked : (List.range' 870656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1700_3_checked : (List.range' 870784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1700_range (index : Nat) (lower : 870400 ≤ index) (upper : index < 870912) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 870656 then
    if cut : index < 870528 then
      exact segment_sound _ 870400 128 Restriction1700_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 870528 128 Restriction1700_1_checked index (by omega) (by omega)
  else
    if cut : index < 870784 then
      exact segment_sound _ 870656 128 Restriction1700_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 870784 128 Restriction1700_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
