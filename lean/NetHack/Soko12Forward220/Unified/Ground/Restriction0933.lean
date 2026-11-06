import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0933_0_checked : (List.range' 477696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0933_1_checked : (List.range' 477824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0933_2_checked : (List.range' 477952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0933_3_checked : (List.range' 478080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0933_range (index : Nat) (lower : 477696 ≤ index) (upper : index < 478208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 477952 then
    if cut : index < 477824 then
      exact segment_sound _ 477696 128 Restriction0933_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 477824 128 Restriction0933_1_checked index (by omega) (by omega)
  else
    if cut : index < 478080 then
      exact segment_sound _ 477952 128 Restriction0933_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 478080 128 Restriction0933_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
