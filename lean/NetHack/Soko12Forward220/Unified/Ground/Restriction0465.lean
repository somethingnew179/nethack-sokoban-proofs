import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0465_0_checked : (List.range' 238080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0465_1_checked : (List.range' 238208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0465_2_checked : (List.range' 238336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0465_3_checked : (List.range' 238464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0465_range (index : Nat) (lower : 238080 ≤ index) (upper : index < 238592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 238336 then
    if cut : index < 238208 then
      exact segment_sound _ 238080 128 Restriction0465_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 238208 128 Restriction0465_1_checked index (by omega) (by omega)
  else
    if cut : index < 238464 then
      exact segment_sound _ 238336 128 Restriction0465_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 238464 128 Restriction0465_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
