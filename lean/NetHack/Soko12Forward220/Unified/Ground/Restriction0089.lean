import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0089_0_checked : (List.range' 45568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0089_1_checked : (List.range' 45696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0089_2_checked : (List.range' 45824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0089_3_checked : (List.range' 45952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0089_range (index : Nat) (lower : 45568 ≤ index) (upper : index < 46080) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 45824 then
    if cut : index < 45696 then
      exact segment_sound _ 45568 128 Restriction0089_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 45696 128 Restriction0089_1_checked index (by omega) (by omega)
  else
    if cut : index < 45952 then
      exact segment_sound _ 45824 128 Restriction0089_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 45952 128 Restriction0089_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
