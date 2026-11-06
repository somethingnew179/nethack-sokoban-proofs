import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0865_0_checked : (List.range' 442880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0865_1_checked : (List.range' 443008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0865_2_checked : (List.range' 443136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0865_3_checked : (List.range' 443264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0865_range (index : Nat) (lower : 442880 ≤ index) (upper : index < 443392) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 443136 then
    if cut : index < 443008 then
      exact segment_sound _ 442880 128 Restriction0865_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 443008 128 Restriction0865_1_checked index (by omega) (by omega)
  else
    if cut : index < 443264 then
      exact segment_sound _ 443136 128 Restriction0865_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 443264 128 Restriction0865_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
