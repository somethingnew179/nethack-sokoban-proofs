import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1076_0_checked : (List.range' 550912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1076_1_checked : (List.range' 551040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1076_2_checked : (List.range' 551168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1076_3_checked : (List.range' 551296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1076_range (index : Nat) (lower : 550912 ≤ index) (upper : index < 551424) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 551168 then
    if cut : index < 551040 then
      exact segment_sound _ 550912 128 Restriction1076_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 551040 128 Restriction1076_1_checked index (by omega) (by omega)
  else
    if cut : index < 551296 then
      exact segment_sound _ 551168 128 Restriction1076_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 551296 128 Restriction1076_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
