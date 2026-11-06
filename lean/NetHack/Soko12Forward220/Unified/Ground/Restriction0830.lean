import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0830_0_checked : (List.range' 424960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0830_1_checked : (List.range' 425088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0830_2_checked : (List.range' 425216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0830_3_checked : (List.range' 425344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0830_range (index : Nat) (lower : 424960 ≤ index) (upper : index < 425472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 425216 then
    if cut : index < 425088 then
      exact segment_sound _ 424960 128 Restriction0830_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 425088 128 Restriction0830_1_checked index (by omega) (by omega)
  else
    if cut : index < 425344 then
      exact segment_sound _ 425216 128 Restriction0830_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 425344 128 Restriction0830_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
