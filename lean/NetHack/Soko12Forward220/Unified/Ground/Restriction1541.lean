import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1541_0_checked : (List.range' 788992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1541_1_checked : (List.range' 789120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1541_2_checked : (List.range' 789248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1541_3_checked : (List.range' 789376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1541_range (index : Nat) (lower : 788992 ≤ index) (upper : index < 789504) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 789248 then
    if cut : index < 789120 then
      exact segment_sound _ 788992 128 Restriction1541_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 789120 128 Restriction1541_1_checked index (by omega) (by omega)
  else
    if cut : index < 789376 then
      exact segment_sound _ 789248 128 Restriction1541_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 789376 128 Restriction1541_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
