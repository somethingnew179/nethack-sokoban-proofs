import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0989_0_checked : (List.range' 506368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0989_1_checked : (List.range' 506496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0989_2_checked : (List.range' 506624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0989_3_checked : (List.range' 506752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0989_range (index : Nat) (lower : 506368 ≤ index) (upper : index < 506880) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 506624 then
    if cut : index < 506496 then
      exact segment_sound _ 506368 128 Restriction0989_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 506496 128 Restriction0989_1_checked index (by omega) (by omega)
  else
    if cut : index < 506752 then
      exact segment_sound _ 506624 128 Restriction0989_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 506752 128 Restriction0989_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
