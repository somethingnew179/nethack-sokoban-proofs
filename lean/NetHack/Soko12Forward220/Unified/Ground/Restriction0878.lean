import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0878_0_checked : (List.range' 449536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0878_1_checked : (List.range' 449664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0878_2_checked : (List.range' 449792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0878_3_checked : (List.range' 449920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0878_range (index : Nat) (lower : 449536 ≤ index) (upper : index < 450048) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 449792 then
    if cut : index < 449664 then
      exact segment_sound _ 449536 128 Restriction0878_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 449664 128 Restriction0878_1_checked index (by omega) (by omega)
  else
    if cut : index < 449920 then
      exact segment_sound _ 449792 128 Restriction0878_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 449920 128 Restriction0878_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
