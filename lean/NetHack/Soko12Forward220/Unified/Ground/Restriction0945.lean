import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0945_0_checked : (List.range' 483840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0945_1_checked : (List.range' 483968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0945_2_checked : (List.range' 484096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0945_3_checked : (List.range' 484224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0945_range (index : Nat) (lower : 483840 ≤ index) (upper : index < 484352) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 484096 then
    if cut : index < 483968 then
      exact segment_sound _ 483840 128 Restriction0945_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 483968 128 Restriction0945_1_checked index (by omega) (by omega)
  else
    if cut : index < 484224 then
      exact segment_sound _ 484096 128 Restriction0945_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 484224 128 Restriction0945_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
