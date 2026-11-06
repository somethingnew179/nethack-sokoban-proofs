import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0793_0_checked : (List.range' 406016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0793_1_checked : (List.range' 406144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0793_2_checked : (List.range' 406272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0793_3_checked : (List.range' 406400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0793_range (index : Nat) (lower : 406016 ≤ index) (upper : index < 406528) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 406272 then
    if cut : index < 406144 then
      exact segment_sound _ 406016 128 Restriction0793_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 406144 128 Restriction0793_1_checked index (by omega) (by omega)
  else
    if cut : index < 406400 then
      exact segment_sound _ 406272 128 Restriction0793_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 406400 128 Restriction0793_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
