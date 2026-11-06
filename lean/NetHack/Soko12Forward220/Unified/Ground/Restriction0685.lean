import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0685_0_checked : (List.range' 350720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0685_1_checked : (List.range' 350848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0685_2_checked : (List.range' 350976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0685_3_checked : (List.range' 351104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0685_range (index : Nat) (lower : 350720 ≤ index) (upper : index < 351232) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 350976 then
    if cut : index < 350848 then
      exact segment_sound _ 350720 128 Restriction0685_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 350848 128 Restriction0685_1_checked index (by omega) (by omega)
  else
    if cut : index < 351104 then
      exact segment_sound _ 350976 128 Restriction0685_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 351104 128 Restriction0685_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
