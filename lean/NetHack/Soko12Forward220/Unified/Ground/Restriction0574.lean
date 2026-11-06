import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0574_0_checked : (List.range' 293888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0574_1_checked : (List.range' 294016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0574_2_checked : (List.range' 294144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0574_3_checked : (List.range' 294272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0574_range (index : Nat) (lower : 293888 ≤ index) (upper : index < 294400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 294144 then
    if cut : index < 294016 then
      exact segment_sound _ 293888 128 Restriction0574_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 294016 128 Restriction0574_1_checked index (by omega) (by omega)
  else
    if cut : index < 294272 then
      exact segment_sound _ 294144 128 Restriction0574_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 294272 128 Restriction0574_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
