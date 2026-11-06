import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0254_0_checked : (List.range' 130048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0254_1_checked : (List.range' 130176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0254_2_checked : (List.range' 130304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0254_3_checked : (List.range' 130432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0254_range (index : Nat) (lower : 130048 ≤ index) (upper : index < 130560) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 130304 then
    if cut : index < 130176 then
      exact segment_sound _ 130048 128 Restriction0254_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 130176 128 Restriction0254_1_checked index (by omega) (by omega)
  else
    if cut : index < 130432 then
      exact segment_sound _ 130304 128 Restriction0254_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 130432 128 Restriction0254_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
