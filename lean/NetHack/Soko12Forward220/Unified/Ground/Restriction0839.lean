import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0839_0_checked : (List.range' 429568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0839_1_checked : (List.range' 429696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0839_2_checked : (List.range' 429824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0839_3_checked : (List.range' 429952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0839_range (index : Nat) (lower : 429568 ≤ index) (upper : index < 430080) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 429824 then
    if cut : index < 429696 then
      exact segment_sound _ 429568 128 Restriction0839_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 429696 128 Restriction0839_1_checked index (by omega) (by omega)
  else
    if cut : index < 429952 then
      exact segment_sound _ 429824 128 Restriction0839_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 429952 128 Restriction0839_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
