import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1989_0_checked : (List.range' 1018368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1989_1_checked : (List.range' 1018496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1989_2_checked : (List.range' 1018624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1989_3_checked : (List.range' 1018752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1989_range (index : Nat) (lower : 1018368 ≤ index) (upper : index < 1018880) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1018624 then
    if cut : index < 1018496 then
      exact segment_sound _ 1018368 128 Restriction1989_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1018496 128 Restriction1989_1_checked index (by omega) (by omega)
  else
    if cut : index < 1018752 then
      exact segment_sound _ 1018624 128 Restriction1989_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1018752 128 Restriction1989_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
