import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0956_0_checked : (List.range' 489472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0956_1_checked : (List.range' 489600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0956_2_checked : (List.range' 489728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0956_3_checked : (List.range' 489856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0956_range (index : Nat) (lower : 489472 ≤ index) (upper : index < 489984) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 489728 then
    if cut : index < 489600 then
      exact segment_sound _ 489472 128 Restriction0956_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 489600 128 Restriction0956_1_checked index (by omega) (by omega)
  else
    if cut : index < 489856 then
      exact segment_sound _ 489728 128 Restriction0956_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 489856 128 Restriction0956_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
