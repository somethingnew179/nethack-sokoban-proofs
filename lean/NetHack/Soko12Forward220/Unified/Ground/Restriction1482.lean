import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1482_0_checked : (List.range' 758784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1482_1_checked : (List.range' 758912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1482_2_checked : (List.range' 759040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1482_3_checked : (List.range' 759168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1482_range (index : Nat) (lower : 758784 ≤ index) (upper : index < 759296) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 759040 then
    if cut : index < 758912 then
      exact segment_sound _ 758784 128 Restriction1482_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 758912 128 Restriction1482_1_checked index (by omega) (by omega)
  else
    if cut : index < 759168 then
      exact segment_sound _ 759040 128 Restriction1482_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 759168 128 Restriction1482_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
