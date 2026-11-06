import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0977_0_checked : (List.range' 500224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0977_1_checked : (List.range' 500352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0977_2_checked : (List.range' 500480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0977_3_checked : (List.range' 500608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0977_range (index : Nat) (lower : 500224 ≤ index) (upper : index < 500736) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 500480 then
    if cut : index < 500352 then
      exact segment_sound _ 500224 128 Restriction0977_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 500352 128 Restriction0977_1_checked index (by omega) (by omega)
  else
    if cut : index < 500608 then
      exact segment_sound _ 500480 128 Restriction0977_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 500608 128 Restriction0977_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
