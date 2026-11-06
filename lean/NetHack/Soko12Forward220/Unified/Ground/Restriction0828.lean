import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0828_0_checked : (List.range' 423936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0828_1_checked : (List.range' 424064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0828_2_checked : (List.range' 424192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0828_3_checked : (List.range' 424320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0828_range (index : Nat) (lower : 423936 ≤ index) (upper : index < 424448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 424192 then
    if cut : index < 424064 then
      exact segment_sound _ 423936 128 Restriction0828_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 424064 128 Restriction0828_1_checked index (by omega) (by omega)
  else
    if cut : index < 424320 then
      exact segment_sound _ 424192 128 Restriction0828_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 424320 128 Restriction0828_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
