import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0934_0_checked : (List.range' 478208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0934_1_checked : (List.range' 478336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0934_2_checked : (List.range' 478464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0934_3_checked : (List.range' 478592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0934_range (index : Nat) (lower : 478208 ≤ index) (upper : index < 478720) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 478464 then
    if cut : index < 478336 then
      exact segment_sound _ 478208 128 Restriction0934_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 478336 128 Restriction0934_1_checked index (by omega) (by omega)
  else
    if cut : index < 478592 then
      exact segment_sound _ 478464 128 Restriction0934_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 478592 128 Restriction0934_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
