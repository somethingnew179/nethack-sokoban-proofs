import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0896_0_checked : (List.range' 458752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0896_1_checked : (List.range' 458880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0896_2_checked : (List.range' 459008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0896_3_checked : (List.range' 459136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0896_range (index : Nat) (lower : 458752 ≤ index) (upper : index < 459264) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 459008 then
    if cut : index < 458880 then
      exact segment_sound _ 458752 128 Restriction0896_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 458880 128 Restriction0896_1_checked index (by omega) (by omega)
  else
    if cut : index < 459136 then
      exact segment_sound _ 459008 128 Restriction0896_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 459136 128 Restriction0896_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
