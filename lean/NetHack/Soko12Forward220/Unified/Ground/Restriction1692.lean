import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1692_0_checked : (List.range' 866304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1692_1_checked : (List.range' 866432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1692_2_checked : (List.range' 866560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1692_3_checked : (List.range' 866688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1692_range (index : Nat) (lower : 866304 ≤ index) (upper : index < 866816) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 866560 then
    if cut : index < 866432 then
      exact segment_sound _ 866304 128 Restriction1692_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 866432 128 Restriction1692_1_checked index (by omega) (by omega)
  else
    if cut : index < 866688 then
      exact segment_sound _ 866560 128 Restriction1692_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 866688 128 Restriction1692_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
