import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1864_0_checked : (List.range' 954368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1864_1_checked : (List.range' 954496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1864_2_checked : (List.range' 954624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1864_3_checked : (List.range' 954752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1864_range (index : Nat) (lower : 954368 ≤ index) (upper : index < 954880) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 954624 then
    if cut : index < 954496 then
      exact segment_sound _ 954368 128 Restriction1864_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 954496 128 Restriction1864_1_checked index (by omega) (by omega)
  else
    if cut : index < 954752 then
      exact segment_sound _ 954624 128 Restriction1864_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 954752 128 Restriction1864_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
