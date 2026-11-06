import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0222_0_checked : (List.range' 113664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0222_1_checked : (List.range' 113792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0222_2_checked : (List.range' 113920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0222_3_checked : (List.range' 114048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0222_range (index : Nat) (lower : 113664 ≤ index) (upper : index < 114176) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 113920 then
    if cut : index < 113792 then
      exact segment_sound _ 113664 128 Restriction0222_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 113792 128 Restriction0222_1_checked index (by omega) (by omega)
  else
    if cut : index < 114048 then
      exact segment_sound _ 113920 128 Restriction0222_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 114048 128 Restriction0222_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
