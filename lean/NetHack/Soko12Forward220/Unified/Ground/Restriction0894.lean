import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0894_0_checked : (List.range' 457728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0894_1_checked : (List.range' 457856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0894_2_checked : (List.range' 457984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0894_3_checked : (List.range' 458112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0894_range (index : Nat) (lower : 457728 ≤ index) (upper : index < 458240) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 457984 then
    if cut : index < 457856 then
      exact segment_sound _ 457728 128 Restriction0894_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 457856 128 Restriction0894_1_checked index (by omega) (by omega)
  else
    if cut : index < 458112 then
      exact segment_sound _ 457984 128 Restriction0894_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 458112 128 Restriction0894_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
