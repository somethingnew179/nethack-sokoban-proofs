import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0955_0_checked : (List.range' 488960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0955_1_checked : (List.range' 489088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0955_2_checked : (List.range' 489216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0955_3_checked : (List.range' 489344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0955_range (index : Nat) (lower : 488960 ≤ index) (upper : index < 489472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 489216 then
    if cut : index < 489088 then
      exact segment_sound _ 488960 128 Restriction0955_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 489088 128 Restriction0955_1_checked index (by omega) (by omega)
  else
    if cut : index < 489344 then
      exact segment_sound _ 489216 128 Restriction0955_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 489344 128 Restriction0955_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
