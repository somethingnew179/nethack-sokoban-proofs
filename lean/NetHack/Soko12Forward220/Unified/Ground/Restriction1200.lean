import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1200_0_checked : (List.range' 614400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1200_1_checked : (List.range' 614528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1200_2_checked : (List.range' 614656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1200_3_checked : (List.range' 614784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1200_range (index : Nat) (lower : 614400 ≤ index) (upper : index < 614912) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 614656 then
    if cut : index < 614528 then
      exact segment_sound _ 614400 128 Restriction1200_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 614528 128 Restriction1200_1_checked index (by omega) (by omega)
  else
    if cut : index < 614784 then
      exact segment_sound _ 614656 128 Restriction1200_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 614784 128 Restriction1200_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
