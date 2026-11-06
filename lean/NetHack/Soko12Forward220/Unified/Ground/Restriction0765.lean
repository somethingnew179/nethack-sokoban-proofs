import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0765_0_checked : (List.range' 391680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0765_1_checked : (List.range' 391808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0765_2_checked : (List.range' 391936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0765_3_checked : (List.range' 392064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0765_range (index : Nat) (lower : 391680 ≤ index) (upper : index < 392192) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 391936 then
    if cut : index < 391808 then
      exact segment_sound _ 391680 128 Restriction0765_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 391808 128 Restriction0765_1_checked index (by omega) (by omega)
  else
    if cut : index < 392064 then
      exact segment_sound _ 391936 128 Restriction0765_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 392064 128 Restriction0765_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
