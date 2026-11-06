import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1593_0_checked : (List.range' 815616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1593_1_checked : (List.range' 815744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1593_2_checked : (List.range' 815872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1593_3_checked : (List.range' 816000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1593_range (index : Nat) (lower : 815616 ≤ index) (upper : index < 816128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 815872 then
    if cut : index < 815744 then
      exact segment_sound _ 815616 128 Restriction1593_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 815744 128 Restriction1593_1_checked index (by omega) (by omega)
  else
    if cut : index < 816000 then
      exact segment_sound _ 815872 128 Restriction1593_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 816000 128 Restriction1593_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
