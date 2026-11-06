import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0998_0_checked : (List.range' 510976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0998_1_checked : (List.range' 511104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0998_2_checked : (List.range' 511232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0998_3_checked : (List.range' 511360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0998_range (index : Nat) (lower : 510976 ≤ index) (upper : index < 511488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 511232 then
    if cut : index < 511104 then
      exact segment_sound _ 510976 128 Restriction0998_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 511104 128 Restriction0998_1_checked index (by omega) (by omega)
  else
    if cut : index < 511360 then
      exact segment_sound _ 511232 128 Restriction0998_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 511360 128 Restriction0998_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
