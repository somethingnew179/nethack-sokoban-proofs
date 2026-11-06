import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1155_0_checked : (List.range' 591360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1155_1_checked : (List.range' 591488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1155_2_checked : (List.range' 591616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1155_3_checked : (List.range' 591744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1155_range (index : Nat) (lower : 591360 ≤ index) (upper : index < 591872) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 591616 then
    if cut : index < 591488 then
      exact segment_sound _ 591360 128 Restriction1155_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 591488 128 Restriction1155_1_checked index (by omega) (by omega)
  else
    if cut : index < 591744 then
      exact segment_sound _ 591616 128 Restriction1155_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 591744 128 Restriction1155_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
