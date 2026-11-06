import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0326_0_checked : (List.range' 166912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0326_1_checked : (List.range' 167040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0326_2_checked : (List.range' 167168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0326_3_checked : (List.range' 167296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0326_range (index : Nat) (lower : 166912 ≤ index) (upper : index < 167424) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 167168 then
    if cut : index < 167040 then
      exact segment_sound _ 166912 128 Restriction0326_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 167040 128 Restriction0326_1_checked index (by omega) (by omega)
  else
    if cut : index < 167296 then
      exact segment_sound _ 167168 128 Restriction0326_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 167296 128 Restriction0326_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
