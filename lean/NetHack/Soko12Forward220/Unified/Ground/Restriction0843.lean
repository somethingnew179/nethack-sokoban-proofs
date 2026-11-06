import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0843_0_checked : (List.range' 431616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0843_1_checked : (List.range' 431744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0843_2_checked : (List.range' 431872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0843_3_checked : (List.range' 432000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0843_range (index : Nat) (lower : 431616 ≤ index) (upper : index < 432128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 431872 then
    if cut : index < 431744 then
      exact segment_sound _ 431616 128 Restriction0843_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 431744 128 Restriction0843_1_checked index (by omega) (by omega)
  else
    if cut : index < 432000 then
      exact segment_sound _ 431872 128 Restriction0843_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 432000 128 Restriction0843_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
