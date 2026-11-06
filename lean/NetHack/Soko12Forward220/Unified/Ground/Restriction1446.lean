import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1446_0_checked : (List.range' 740352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1446_1_checked : (List.range' 740480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1446_2_checked : (List.range' 740608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1446_3_checked : (List.range' 740736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1446_range (index : Nat) (lower : 740352 ≤ index) (upper : index < 740864) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 740608 then
    if cut : index < 740480 then
      exact segment_sound _ 740352 128 Restriction1446_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 740480 128 Restriction1446_1_checked index (by omega) (by omega)
  else
    if cut : index < 740736 then
      exact segment_sound _ 740608 128 Restriction1446_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 740736 128 Restriction1446_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
