import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1677_0_checked : (List.range' 858624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1677_1_checked : (List.range' 858752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1677_2_checked : (List.range' 858880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1677_3_checked : (List.range' 859008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1677_range (index : Nat) (lower : 858624 ≤ index) (upper : index < 859136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 858880 then
    if cut : index < 858752 then
      exact segment_sound _ 858624 128 Restriction1677_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 858752 128 Restriction1677_1_checked index (by omega) (by omega)
  else
    if cut : index < 859008 then
      exact segment_sound _ 858880 128 Restriction1677_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 859008 128 Restriction1677_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
