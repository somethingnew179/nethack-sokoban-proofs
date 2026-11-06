import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0534_0_checked : (List.range' 273408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0534_1_checked : (List.range' 273536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0534_2_checked : (List.range' 273664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0534_3_checked : (List.range' 273792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0534_range (index : Nat) (lower : 273408 ≤ index) (upper : index < 273920) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 273664 then
    if cut : index < 273536 then
      exact segment_sound _ 273408 128 Restriction0534_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 273536 128 Restriction0534_1_checked index (by omega) (by omega)
  else
    if cut : index < 273792 then
      exact segment_sound _ 273664 128 Restriction0534_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 273792 128 Restriction0534_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
