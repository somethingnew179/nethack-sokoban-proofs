import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0216_0_checked : (List.range' 110592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0216_1_checked : (List.range' 110720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0216_2_checked : (List.range' 110848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0216_3_checked : (List.range' 110976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0216_range (index : Nat) (lower : 110592 ≤ index) (upper : index < 111104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 110848 then
    if cut : index < 110720 then
      exact segment_sound _ 110592 128 Restriction0216_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 110720 128 Restriction0216_1_checked index (by omega) (by omega)
  else
    if cut : index < 110976 then
      exact segment_sound _ 110848 128 Restriction0216_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 110976 128 Restriction0216_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
