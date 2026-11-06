import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0667_0_checked : (List.range' 341504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0667_1_checked : (List.range' 341632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0667_2_checked : (List.range' 341760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0667_3_checked : (List.range' 341888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0667_range (index : Nat) (lower : 341504 ≤ index) (upper : index < 342016) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 341760 then
    if cut : index < 341632 then
      exact segment_sound _ 341504 128 Restriction0667_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 341632 128 Restriction0667_1_checked index (by omega) (by omega)
  else
    if cut : index < 341888 then
      exact segment_sound _ 341760 128 Restriction0667_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 341888 128 Restriction0667_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
