import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0415_0_checked : (List.range' 212480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0415_1_checked : (List.range' 212608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0415_2_checked : (List.range' 212736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0415_3_checked : (List.range' 212864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0415_range (index : Nat) (lower : 212480 ≤ index) (upper : index < 212992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 212736 then
    if cut : index < 212608 then
      exact segment_sound _ 212480 128 Restriction0415_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 212608 128 Restriction0415_1_checked index (by omega) (by omega)
  else
    if cut : index < 212864 then
      exact segment_sound _ 212736 128 Restriction0415_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 212864 128 Restriction0415_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
