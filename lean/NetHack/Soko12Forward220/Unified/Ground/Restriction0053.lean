import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0053_0_checked : (List.range' 27136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0053_1_checked : (List.range' 27264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0053_2_checked : (List.range' 27392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0053_3_checked : (List.range' 27520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0053_range (index : Nat) (lower : 27136 ≤ index) (upper : index < 27648) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 27392 then
    if cut : index < 27264 then
      exact segment_sound _ 27136 128 Restriction0053_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 27264 128 Restriction0053_1_checked index (by omega) (by omega)
  else
    if cut : index < 27520 then
      exact segment_sound _ 27392 128 Restriction0053_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 27520 128 Restriction0053_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
