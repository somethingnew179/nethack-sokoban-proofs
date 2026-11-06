import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0884_0_checked : (List.range' 452608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0884_1_checked : (List.range' 452736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0884_2_checked : (List.range' 452864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0884_3_checked : (List.range' 452992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0884_range (index : Nat) (lower : 452608 ≤ index) (upper : index < 453120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 452864 then
    if cut : index < 452736 then
      exact segment_sound _ 452608 128 Restriction0884_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 452736 128 Restriction0884_1_checked index (by omega) (by omega)
  else
    if cut : index < 452992 then
      exact segment_sound _ 452864 128 Restriction0884_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 452992 128 Restriction0884_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
