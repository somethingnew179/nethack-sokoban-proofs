import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0915_0_checked : (List.range' 468480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0915_1_checked : (List.range' 468608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0915_2_checked : (List.range' 468736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0915_3_checked : (List.range' 468864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0915_range (index : Nat) (lower : 468480 ≤ index) (upper : index < 468992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 468736 then
    if cut : index < 468608 then
      exact segment_sound _ 468480 128 Restriction0915_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 468608 128 Restriction0915_1_checked index (by omega) (by omega)
  else
    if cut : index < 468864 then
      exact segment_sound _ 468736 128 Restriction0915_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 468864 128 Restriction0915_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
