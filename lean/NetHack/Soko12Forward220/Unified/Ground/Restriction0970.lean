import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0970_0_checked : (List.range' 496640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0970_1_checked : (List.range' 496768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0970_2_checked : (List.range' 496896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0970_3_checked : (List.range' 497024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0970_range (index : Nat) (lower : 496640 ≤ index) (upper : index < 497152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 496896 then
    if cut : index < 496768 then
      exact segment_sound _ 496640 128 Restriction0970_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 496768 128 Restriction0970_1_checked index (by omega) (by omega)
  else
    if cut : index < 497024 then
      exact segment_sound _ 496896 128 Restriction0970_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 497024 128 Restriction0970_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
