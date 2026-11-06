import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0617_0_checked : (List.range' 315904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0617_1_checked : (List.range' 316032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0617_2_checked : (List.range' 316160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0617_3_checked : (List.range' 316288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0617_range (index : Nat) (lower : 315904 ≤ index) (upper : index < 316416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 316160 then
    if cut : index < 316032 then
      exact segment_sound _ 315904 128 Restriction0617_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 316032 128 Restriction0617_1_checked index (by omega) (by omega)
  else
    if cut : index < 316288 then
      exact segment_sound _ 316160 128 Restriction0617_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 316288 128 Restriction0617_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
