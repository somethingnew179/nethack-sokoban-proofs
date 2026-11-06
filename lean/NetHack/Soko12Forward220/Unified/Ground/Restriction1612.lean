import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1612_0_checked : (List.range' 825344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1612_1_checked : (List.range' 825472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1612_2_checked : (List.range' 825600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1612_3_checked : (List.range' 825728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1612_range (index : Nat) (lower : 825344 ≤ index) (upper : index < 825856) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 825600 then
    if cut : index < 825472 then
      exact segment_sound _ 825344 128 Restriction1612_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 825472 128 Restriction1612_1_checked index (by omega) (by omega)
  else
    if cut : index < 825728 then
      exact segment_sound _ 825600 128 Restriction1612_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 825728 128 Restriction1612_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
