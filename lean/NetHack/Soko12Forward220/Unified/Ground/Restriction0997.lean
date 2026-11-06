import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0997_0_checked : (List.range' 510464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0997_1_checked : (List.range' 510592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0997_2_checked : (List.range' 510720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0997_3_checked : (List.range' 510848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0997_range (index : Nat) (lower : 510464 ≤ index) (upper : index < 510976) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 510720 then
    if cut : index < 510592 then
      exact segment_sound _ 510464 128 Restriction0997_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 510592 128 Restriction0997_1_checked index (by omega) (by omega)
  else
    if cut : index < 510848 then
      exact segment_sound _ 510720 128 Restriction0997_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 510848 128 Restriction0997_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
