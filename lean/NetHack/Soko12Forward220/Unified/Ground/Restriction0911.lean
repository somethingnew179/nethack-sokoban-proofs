import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0911_0_checked : (List.range' 466432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0911_1_checked : (List.range' 466560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0911_2_checked : (List.range' 466688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0911_3_checked : (List.range' 466816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0911_range (index : Nat) (lower : 466432 ≤ index) (upper : index < 466944) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 466688 then
    if cut : index < 466560 then
      exact segment_sound _ 466432 128 Restriction0911_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 466560 128 Restriction0911_1_checked index (by omega) (by omega)
  else
    if cut : index < 466816 then
      exact segment_sound _ 466688 128 Restriction0911_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 466816 128 Restriction0911_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
