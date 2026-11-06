import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1481_0_checked : (List.range' 758272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1481_1_checked : (List.range' 758400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1481_2_checked : (List.range' 758528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1481_3_checked : (List.range' 758656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1481_range (index : Nat) (lower : 758272 ≤ index) (upper : index < 758784) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 758528 then
    if cut : index < 758400 then
      exact segment_sound _ 758272 128 Restriction1481_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 758400 128 Restriction1481_1_checked index (by omega) (by omega)
  else
    if cut : index < 758656 then
      exact segment_sound _ 758528 128 Restriction1481_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 758656 128 Restriction1481_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
