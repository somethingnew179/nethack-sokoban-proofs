import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0351_0_checked : (List.range' 179712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0351_1_checked : (List.range' 179840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0351_2_checked : (List.range' 179968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0351_3_checked : (List.range' 180096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0351_range (index : Nat) (lower : 179712 ≤ index) (upper : index < 180224) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 179968 then
    if cut : index < 179840 then
      exact segment_sound _ 179712 128 Restriction0351_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 179840 128 Restriction0351_1_checked index (by omega) (by omega)
  else
    if cut : index < 180096 then
      exact segment_sound _ 179968 128 Restriction0351_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 180096 128 Restriction0351_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
