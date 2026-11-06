import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0995_0_checked : (List.range' 509440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0995_1_checked : (List.range' 509568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0995_2_checked : (List.range' 509696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0995_3_checked : (List.range' 509824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0995_range (index : Nat) (lower : 509440 ≤ index) (upper : index < 509952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 509696 then
    if cut : index < 509568 then
      exact segment_sound _ 509440 128 Restriction0995_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 509568 128 Restriction0995_1_checked index (by omega) (by omega)
  else
    if cut : index < 509824 then
      exact segment_sound _ 509696 128 Restriction0995_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 509824 128 Restriction0995_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
