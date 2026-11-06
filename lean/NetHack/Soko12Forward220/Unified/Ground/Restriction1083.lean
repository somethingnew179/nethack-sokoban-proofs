import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1083_0_checked : (List.range' 554496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1083_1_checked : (List.range' 554624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1083_2_checked : (List.range' 554752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1083_3_checked : (List.range' 554880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1083_range (index : Nat) (lower : 554496 ≤ index) (upper : index < 555008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 554752 then
    if cut : index < 554624 then
      exact segment_sound _ 554496 128 Restriction1083_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 554624 128 Restriction1083_1_checked index (by omega) (by omega)
  else
    if cut : index < 554880 then
      exact segment_sound _ 554752 128 Restriction1083_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 554880 128 Restriction1083_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
