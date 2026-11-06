import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0249_0_checked : (List.range' 127488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0249_1_checked : (List.range' 127616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0249_2_checked : (List.range' 127744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0249_3_checked : (List.range' 127872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0249_range (index : Nat) (lower : 127488 ≤ index) (upper : index < 128000) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 127744 then
    if cut : index < 127616 then
      exact segment_sound _ 127488 128 Restriction0249_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 127616 128 Restriction0249_1_checked index (by omega) (by omega)
  else
    if cut : index < 127872 then
      exact segment_sound _ 127744 128 Restriction0249_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 127872 128 Restriction0249_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
