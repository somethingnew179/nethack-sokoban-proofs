import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0751_0_checked : (List.range' 384512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0751_1_checked : (List.range' 384640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0751_2_checked : (List.range' 384768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0751_3_checked : (List.range' 384896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0751_range (index : Nat) (lower : 384512 ≤ index) (upper : index < 385024) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 384768 then
    if cut : index < 384640 then
      exact segment_sound _ 384512 128 Restriction0751_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 384640 128 Restriction0751_1_checked index (by omega) (by omega)
  else
    if cut : index < 384896 then
      exact segment_sound _ 384768 128 Restriction0751_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 384896 128 Restriction0751_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
