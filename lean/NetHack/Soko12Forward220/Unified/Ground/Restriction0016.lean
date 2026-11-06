import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0016_0_checked : (List.range' 8192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0016_1_checked : (List.range' 8320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0016_2_checked : (List.range' 8448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0016_3_checked : (List.range' 8576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0016_range (index : Nat) (lower : 8192 ≤ index) (upper : index < 8704) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 8448 then
    if cut : index < 8320 then
      exact segment_sound _ 8192 128 Restriction0016_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 8320 128 Restriction0016_1_checked index (by omega) (by omega)
  else
    if cut : index < 8576 then
      exact segment_sound _ 8448 128 Restriction0016_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 8576 128 Restriction0016_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
