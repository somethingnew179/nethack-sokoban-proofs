import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0374_0_checked : (List.range' 191488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0374_1_checked : (List.range' 191616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0374_2_checked : (List.range' 191744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0374_3_checked : (List.range' 191872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0374_range (index : Nat) (lower : 191488 ≤ index) (upper : index < 192000) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 191744 then
    if cut : index < 191616 then
      exact segment_sound _ 191488 128 Restriction0374_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 191616 128 Restriction0374_1_checked index (by omega) (by omega)
  else
    if cut : index < 191872 then
      exact segment_sound _ 191744 128 Restriction0374_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 191872 128 Restriction0374_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
