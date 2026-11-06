import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0567_0_checked : (List.range' 290304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0567_1_checked : (List.range' 290432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0567_2_checked : (List.range' 290560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0567_3_checked : (List.range' 290688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0567_range (index : Nat) (lower : 290304 ≤ index) (upper : index < 290816) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 290560 then
    if cut : index < 290432 then
      exact segment_sound _ 290304 128 Restriction0567_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 290432 128 Restriction0567_1_checked index (by omega) (by omega)
  else
    if cut : index < 290688 then
      exact segment_sound _ 290560 128 Restriction0567_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 290688 128 Restriction0567_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
