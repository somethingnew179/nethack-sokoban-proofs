import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1316_0_checked : (List.range' 673792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1316_1_checked : (List.range' 673920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1316_2_checked : (List.range' 674048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1316_3_checked : (List.range' 674176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1316_range (index : Nat) (lower : 673792 ≤ index) (upper : index < 674304) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 674048 then
    if cut : index < 673920 then
      exact segment_sound _ 673792 128 Restriction1316_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 673920 128 Restriction1316_1_checked index (by omega) (by omega)
  else
    if cut : index < 674176 then
      exact segment_sound _ 674048 128 Restriction1316_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 674176 128 Restriction1316_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
