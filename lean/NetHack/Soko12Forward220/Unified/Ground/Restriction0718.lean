import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0718_0_checked : (List.range' 367616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0718_1_checked : (List.range' 367744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0718_2_checked : (List.range' 367872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0718_3_checked : (List.range' 368000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0718_range (index : Nat) (lower : 367616 ≤ index) (upper : index < 368128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 367872 then
    if cut : index < 367744 then
      exact segment_sound _ 367616 128 Restriction0718_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 367744 128 Restriction0718_1_checked index (by omega) (by omega)
  else
    if cut : index < 368000 then
      exact segment_sound _ 367872 128 Restriction0718_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 368000 128 Restriction0718_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
