import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1052_0_checked : (List.range' 538624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1052_1_checked : (List.range' 538752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1052_2_checked : (List.range' 538880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1052_3_checked : (List.range' 539008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1052_range (index : Nat) (lower : 538624 ≤ index) (upper : index < 539136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 538880 then
    if cut : index < 538752 then
      exact segment_sound _ 538624 128 Restriction1052_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 538752 128 Restriction1052_1_checked index (by omega) (by omega)
  else
    if cut : index < 539008 then
      exact segment_sound _ 538880 128 Restriction1052_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 539008 128 Restriction1052_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
