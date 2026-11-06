import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1243_0_checked : (List.range' 636416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1243_1_checked : (List.range' 636544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1243_2_checked : (List.range' 636672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1243_3_checked : (List.range' 636800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1243_range (index : Nat) (lower : 636416 ≤ index) (upper : index < 636928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 636672 then
    if cut : index < 636544 then
      exact segment_sound _ 636416 128 Restriction1243_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 636544 128 Restriction1243_1_checked index (by omega) (by omega)
  else
    if cut : index < 636800 then
      exact segment_sound _ 636672 128 Restriction1243_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 636800 128 Restriction1243_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
