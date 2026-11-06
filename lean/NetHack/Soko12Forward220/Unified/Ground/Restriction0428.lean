import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0428_0_checked : (List.range' 219136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0428_1_checked : (List.range' 219264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0428_2_checked : (List.range' 219392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0428_3_checked : (List.range' 219520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0428_range (index : Nat) (lower : 219136 ≤ index) (upper : index < 219648) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 219392 then
    if cut : index < 219264 then
      exact segment_sound _ 219136 128 Restriction0428_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 219264 128 Restriction0428_1_checked index (by omega) (by omega)
  else
    if cut : index < 219520 then
      exact segment_sound _ 219392 128 Restriction0428_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 219520 128 Restriction0428_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
