import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1770_0_checked : (List.range' 906240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1770_1_checked : (List.range' 906368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1770_2_checked : (List.range' 906496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1770_3_checked : (List.range' 906624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1770_range (index : Nat) (lower : 906240 ≤ index) (upper : index < 906752) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 906496 then
    if cut : index < 906368 then
      exact segment_sound _ 906240 128 Restriction1770_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 906368 128 Restriction1770_1_checked index (by omega) (by omega)
  else
    if cut : index < 906624 then
      exact segment_sound _ 906496 128 Restriction1770_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 906624 128 Restriction1770_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
