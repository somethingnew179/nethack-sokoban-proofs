import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1628_0_checked : (List.range' 833536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1628_1_checked : (List.range' 833664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1628_2_checked : (List.range' 833792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1628_3_checked : (List.range' 833920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1628_range (index : Nat) (lower : 833536 ≤ index) (upper : index < 834048) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 833792 then
    if cut : index < 833664 then
      exact segment_sound _ 833536 128 Restriction1628_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 833664 128 Restriction1628_1_checked index (by omega) (by omega)
  else
    if cut : index < 833920 then
      exact segment_sound _ 833792 128 Restriction1628_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 833920 128 Restriction1628_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
