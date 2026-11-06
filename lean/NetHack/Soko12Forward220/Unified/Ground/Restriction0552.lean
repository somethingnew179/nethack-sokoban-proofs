import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0552_0_checked : (List.range' 282624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0552_1_checked : (List.range' 282752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0552_2_checked : (List.range' 282880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0552_3_checked : (List.range' 283008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0552_range (index : Nat) (lower : 282624 ≤ index) (upper : index < 283136) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 282880 then
    if cut : index < 282752 then
      exact segment_sound _ 282624 128 Restriction0552_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 282752 128 Restriction0552_1_checked index (by omega) (by omega)
  else
    if cut : index < 283008 then
      exact segment_sound _ 282880 128 Restriction0552_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 283008 128 Restriction0552_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
