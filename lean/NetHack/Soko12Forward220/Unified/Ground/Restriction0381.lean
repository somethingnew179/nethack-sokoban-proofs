import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0381_0_checked : (List.range' 195072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0381_1_checked : (List.range' 195200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0381_2_checked : (List.range' 195328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0381_3_checked : (List.range' 195456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0381_range (index : Nat) (lower : 195072 ≤ index) (upper : index < 195584) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 195328 then
    if cut : index < 195200 then
      exact segment_sound _ 195072 128 Restriction0381_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 195200 128 Restriction0381_1_checked index (by omega) (by omega)
  else
    if cut : index < 195456 then
      exact segment_sound _ 195328 128 Restriction0381_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 195456 128 Restriction0381_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
