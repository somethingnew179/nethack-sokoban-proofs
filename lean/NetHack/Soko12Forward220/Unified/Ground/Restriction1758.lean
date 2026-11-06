import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1758_0_checked : (List.range' 900096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1758_1_checked : (List.range' 900224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1758_2_checked : (List.range' 900352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1758_3_checked : (List.range' 900480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1758_range (index : Nat) (lower : 900096 ≤ index) (upper : index < 900608) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 900352 then
    if cut : index < 900224 then
      exact segment_sound _ 900096 128 Restriction1758_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 900224 128 Restriction1758_1_checked index (by omega) (by omega)
  else
    if cut : index < 900480 then
      exact segment_sound _ 900352 128 Restriction1758_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 900480 128 Restriction1758_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
