import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0743_0_checked : (List.range' 380416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0743_1_checked : (List.range' 380544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0743_2_checked : (List.range' 380672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0743_3_checked : (List.range' 380800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0743_range (index : Nat) (lower : 380416 ≤ index) (upper : index < 380928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 380672 then
    if cut : index < 380544 then
      exact segment_sound _ 380416 128 Restriction0743_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 380544 128 Restriction0743_1_checked index (by omega) (by omega)
  else
    if cut : index < 380800 then
      exact segment_sound _ 380672 128 Restriction0743_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 380800 128 Restriction0743_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
