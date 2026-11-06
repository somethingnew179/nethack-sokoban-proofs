import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0255_0_checked : (List.range' 130560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0255_1_checked : (List.range' 130688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0255_2_checked : (List.range' 130816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0255_3_checked : (List.range' 130944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0255_range (index : Nat) (lower : 130560 ≤ index) (upper : index < 131072) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 130816 then
    if cut : index < 130688 then
      exact segment_sound _ 130560 128 Restriction0255_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 130688 128 Restriction0255_1_checked index (by omega) (by omega)
  else
    if cut : index < 130944 then
      exact segment_sound _ 130816 128 Restriction0255_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 130944 128 Restriction0255_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
