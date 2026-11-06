import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2465_0_checked : (List.range' 1262080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2465_1_checked : (List.range' 1262208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2465_2_checked : (List.range' 1262336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2465_3_checked : (List.range' 1262464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2465_range (index : Nat) (lower : 1262080 ≤ index) (upper : index < 1262592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1262336 then
    if cut : index < 1262208 then
      exact segment_sound _ 1262080 128 Restriction2465_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1262208 128 Restriction2465_1_checked index (by omega) (by omega)
  else
    if cut : index < 1262464 then
      exact segment_sound _ 1262336 128 Restriction2465_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1262464 128 Restriction2465_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
