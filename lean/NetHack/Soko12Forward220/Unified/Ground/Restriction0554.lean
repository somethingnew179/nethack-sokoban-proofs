import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0554_0_checked : (List.range' 283648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0554_1_checked : (List.range' 283776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0554_2_checked : (List.range' 283904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0554_3_checked : (List.range' 284032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0554_range (index : Nat) (lower : 283648 ≤ index) (upper : index < 284160) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 283904 then
    if cut : index < 283776 then
      exact segment_sound _ 283648 128 Restriction0554_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 283776 128 Restriction0554_1_checked index (by omega) (by omega)
  else
    if cut : index < 284032 then
      exact segment_sound _ 283904 128 Restriction0554_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 284032 128 Restriction0554_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
