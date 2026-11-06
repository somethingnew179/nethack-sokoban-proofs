import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1395_0_checked : (List.range' 714240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1395_1_checked : (List.range' 714368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1395_2_checked : (List.range' 714496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1395_3_checked : (List.range' 714624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1395_range (index : Nat) (lower : 714240 ≤ index) (upper : index < 714752) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 714496 then
    if cut : index < 714368 then
      exact segment_sound _ 714240 128 Restriction1395_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 714368 128 Restriction1395_1_checked index (by omega) (by omega)
  else
    if cut : index < 714624 then
      exact segment_sound _ 714496 128 Restriction1395_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 714624 128 Restriction1395_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
