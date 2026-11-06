import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2342_0_checked : (List.range' 1199104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2342_1_checked : (List.range' 1199232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2342_2_checked : (List.range' 1199360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2342_3_checked : (List.range' 1199488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2342_range (index : Nat) (lower : 1199104 ≤ index) (upper : index < 1199616) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1199360 then
    if cut : index < 1199232 then
      exact segment_sound _ 1199104 128 Restriction2342_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1199232 128 Restriction2342_1_checked index (by omega) (by omega)
  else
    if cut : index < 1199488 then
      exact segment_sound _ 1199360 128 Restriction2342_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1199488 128 Restriction2342_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
