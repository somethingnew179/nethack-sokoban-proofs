import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1365_0_checked : (List.range' 698880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1365_1_checked : (List.range' 699008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1365_2_checked : (List.range' 699136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1365_3_checked : (List.range' 699264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1365_range (index : Nat) (lower : 698880 ≤ index) (upper : index < 699392) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 699136 then
    if cut : index < 699008 then
      exact segment_sound _ 698880 128 Restriction1365_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 699008 128 Restriction1365_1_checked index (by omega) (by omega)
  else
    if cut : index < 699264 then
      exact segment_sound _ 699136 128 Restriction1365_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 699264 128 Restriction1365_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
