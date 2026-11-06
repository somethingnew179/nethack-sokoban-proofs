import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0988_0_checked : (List.range' 505856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0988_1_checked : (List.range' 505984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0988_2_checked : (List.range' 506112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0988_3_checked : (List.range' 506240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0988_range (index : Nat) (lower : 505856 ≤ index) (upper : index < 506368) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 506112 then
    if cut : index < 505984 then
      exact segment_sound _ 505856 128 Restriction0988_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 505984 128 Restriction0988_1_checked index (by omega) (by omega)
  else
    if cut : index < 506240 then
      exact segment_sound _ 506112 128 Restriction0988_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 506240 128 Restriction0988_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
