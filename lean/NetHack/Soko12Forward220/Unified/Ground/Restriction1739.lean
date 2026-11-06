import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1739_0_checked : (List.range' 890368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1739_1_checked : (List.range' 890496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1739_2_checked : (List.range' 890624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1739_3_checked : (List.range' 890752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1739_range (index : Nat) (lower : 890368 ≤ index) (upper : index < 890880) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 890624 then
    if cut : index < 890496 then
      exact segment_sound _ 890368 128 Restriction1739_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 890496 128 Restriction1739_1_checked index (by omega) (by omega)
  else
    if cut : index < 890752 then
      exact segment_sound _ 890624 128 Restriction1739_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 890752 128 Restriction1739_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
