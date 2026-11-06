import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1450_0_checked : (List.range' 742400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1450_1_checked : (List.range' 742528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1450_2_checked : (List.range' 742656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1450_3_checked : (List.range' 742784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1450_range (index : Nat) (lower : 742400 ≤ index) (upper : index < 742912) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 742656 then
    if cut : index < 742528 then
      exact segment_sound _ 742400 128 Restriction1450_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 742528 128 Restriction1450_1_checked index (by omega) (by omega)
  else
    if cut : index < 742784 then
      exact segment_sound _ 742656 128 Restriction1450_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 742784 128 Restriction1450_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
