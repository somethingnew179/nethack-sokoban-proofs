import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0747_0_checked : (List.range' 382464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0747_1_checked : (List.range' 382592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0747_2_checked : (List.range' 382720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0747_3_checked : (List.range' 382848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0747_range (index : Nat) (lower : 382464 ≤ index) (upper : index < 382976) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 382720 then
    if cut : index < 382592 then
      exact segment_sound _ 382464 128 Restriction0747_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 382592 128 Restriction0747_1_checked index (by omega) (by omega)
  else
    if cut : index < 382848 then
      exact segment_sound _ 382720 128 Restriction0747_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 382848 128 Restriction0747_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
