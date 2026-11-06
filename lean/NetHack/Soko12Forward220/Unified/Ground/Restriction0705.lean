import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0705_0_checked : (List.range' 360960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0705_1_checked : (List.range' 361088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0705_2_checked : (List.range' 361216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0705_3_checked : (List.range' 361344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0705_range (index : Nat) (lower : 360960 ≤ index) (upper : index < 361472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 361216 then
    if cut : index < 361088 then
      exact segment_sound _ 360960 128 Restriction0705_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 361088 128 Restriction0705_1_checked index (by omega) (by omega)
  else
    if cut : index < 361344 then
      exact segment_sound _ 361216 128 Restriction0705_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 361344 128 Restriction0705_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
