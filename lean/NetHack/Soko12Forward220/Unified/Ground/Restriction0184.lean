import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0184_0_checked : (List.range' 94208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0184_1_checked : (List.range' 94336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0184_2_checked : (List.range' 94464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0184_3_checked : (List.range' 94592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0184_range (index : Nat) (lower : 94208 ≤ index) (upper : index < 94720) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 94464 then
    if cut : index < 94336 then
      exact segment_sound _ 94208 128 Restriction0184_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 94336 128 Restriction0184_1_checked index (by omega) (by omega)
  else
    if cut : index < 94592 then
      exact segment_sound _ 94464 128 Restriction0184_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 94592 128 Restriction0184_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
