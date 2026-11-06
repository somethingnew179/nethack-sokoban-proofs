import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0616_0_checked : (List.range' 315392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0616_1_checked : (List.range' 315520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0616_2_checked : (List.range' 315648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0616_3_checked : (List.range' 315776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0616_range (index : Nat) (lower : 315392 ≤ index) (upper : index < 315904) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 315648 then
    if cut : index < 315520 then
      exact segment_sound _ 315392 128 Restriction0616_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 315520 128 Restriction0616_1_checked index (by omega) (by omega)
  else
    if cut : index < 315776 then
      exact segment_sound _ 315648 128 Restriction0616_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 315776 128 Restriction0616_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
