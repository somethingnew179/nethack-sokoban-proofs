import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0024_0_checked : (List.range' 12288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0024_1_checked : (List.range' 12416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0024_2_checked : (List.range' 12544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0024_3_checked : (List.range' 12672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0024_range (index : Nat) (lower : 12288 ≤ index) (upper : index < 12800) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 12544 then
    if cut : index < 12416 then
      exact segment_sound _ 12288 128 Restriction0024_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 12416 128 Restriction0024_1_checked index (by omega) (by omega)
  else
    if cut : index < 12672 then
      exact segment_sound _ 12544 128 Restriction0024_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 12672 128 Restriction0024_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
