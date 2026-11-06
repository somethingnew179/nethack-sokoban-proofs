import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0771_0_checked : (List.range' 394752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0771_1_checked : (List.range' 394880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0771_2_checked : (List.range' 395008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0771_3_checked : (List.range' 395136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0771_range (index : Nat) (lower : 394752 ≤ index) (upper : index < 395264) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 395008 then
    if cut : index < 394880 then
      exact segment_sound _ 394752 128 Restriction0771_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 394880 128 Restriction0771_1_checked index (by omega) (by omega)
  else
    if cut : index < 395136 then
      exact segment_sound _ 395008 128 Restriction0771_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 395136 128 Restriction0771_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
