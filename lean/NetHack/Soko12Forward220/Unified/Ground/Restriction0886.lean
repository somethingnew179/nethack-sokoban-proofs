import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0886_0_checked : (List.range' 453632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0886_1_checked : (List.range' 453760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0886_2_checked : (List.range' 453888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0886_3_checked : (List.range' 454016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0886_range (index : Nat) (lower : 453632 ≤ index) (upper : index < 454144) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 453888 then
    if cut : index < 453760 then
      exact segment_sound _ 453632 128 Restriction0886_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 453760 128 Restriction0886_1_checked index (by omega) (by omega)
  else
    if cut : index < 454016 then
      exact segment_sound _ 453888 128 Restriction0886_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 454016 128 Restriction0886_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
