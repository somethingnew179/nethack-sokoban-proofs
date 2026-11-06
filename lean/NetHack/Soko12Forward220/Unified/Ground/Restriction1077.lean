import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1077_0_checked : (List.range' 551424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1077_1_checked : (List.range' 551552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1077_2_checked : (List.range' 551680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1077_3_checked : (List.range' 551808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1077_range (index : Nat) (lower : 551424 ≤ index) (upper : index < 551936) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 551680 then
    if cut : index < 551552 then
      exact segment_sound _ 551424 128 Restriction1077_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 551552 128 Restriction1077_1_checked index (by omega) (by omega)
  else
    if cut : index < 551808 then
      exact segment_sound _ 551680 128 Restriction1077_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 551808 128 Restriction1077_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
