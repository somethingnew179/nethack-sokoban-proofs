import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1313_0_checked : (List.range' 672256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1313_1_checked : (List.range' 672384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1313_2_checked : (List.range' 672512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1313_3_checked : (List.range' 672640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1313_range (index : Nat) (lower : 672256 ≤ index) (upper : index < 672768) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 672512 then
    if cut : index < 672384 then
      exact segment_sound _ 672256 128 Restriction1313_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 672384 128 Restriction1313_1_checked index (by omega) (by omega)
  else
    if cut : index < 672640 then
      exact segment_sound _ 672512 128 Restriction1313_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 672640 128 Restriction1313_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
