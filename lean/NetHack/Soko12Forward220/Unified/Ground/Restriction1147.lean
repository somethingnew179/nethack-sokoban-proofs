import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1147_0_checked : (List.range' 587264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1147_1_checked : (List.range' 587392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1147_2_checked : (List.range' 587520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1147_3_checked : (List.range' 587648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1147_range (index : Nat) (lower : 587264 ≤ index) (upper : index < 587776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 587520 then
    if cut : index < 587392 then
      exact segment_sound _ 587264 128 Restriction1147_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 587392 128 Restriction1147_1_checked index (by omega) (by omega)
  else
    if cut : index < 587648 then
      exact segment_sound _ 587520 128 Restriction1147_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 587648 128 Restriction1147_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
