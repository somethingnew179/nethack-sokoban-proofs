import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0996_0_checked : (List.range' 509952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0996_1_checked : (List.range' 510080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0996_2_checked : (List.range' 510208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0996_3_checked : (List.range' 510336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0996_range (index : Nat) (lower : 509952 ≤ index) (upper : index < 510464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 510208 then
    if cut : index < 510080 then
      exact segment_sound _ 509952 128 Restriction0996_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 510080 128 Restriction0996_1_checked index (by omega) (by omega)
  else
    if cut : index < 510336 then
      exact segment_sound _ 510208 128 Restriction0996_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 510336 128 Restriction0996_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
