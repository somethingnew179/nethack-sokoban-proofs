import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1465_0_checked : (List.range' 750080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1465_1_checked : (List.range' 750208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1465_2_checked : (List.range' 750336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1465_3_checked : (List.range' 750464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1465_range (index : Nat) (lower : 750080 ≤ index) (upper : index < 750592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 750336 then
    if cut : index < 750208 then
      exact segment_sound _ 750080 128 Restriction1465_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 750208 128 Restriction1465_1_checked index (by omega) (by omega)
  else
    if cut : index < 750464 then
      exact segment_sound _ 750336 128 Restriction1465_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 750464 128 Restriction1465_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
