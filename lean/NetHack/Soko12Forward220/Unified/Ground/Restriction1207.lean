import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1207_0_checked : (List.range' 617984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1207_1_checked : (List.range' 618112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1207_2_checked : (List.range' 618240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1207_3_checked : (List.range' 618368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1207_range (index : Nat) (lower : 617984 ≤ index) (upper : index < 618496) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 618240 then
    if cut : index < 618112 then
      exact segment_sound _ 617984 128 Restriction1207_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 618112 128 Restriction1207_1_checked index (by omega) (by omega)
  else
    if cut : index < 618368 then
      exact segment_sound _ 618240 128 Restriction1207_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 618368 128 Restriction1207_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
