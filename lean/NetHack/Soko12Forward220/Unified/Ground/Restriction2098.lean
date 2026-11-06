import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2098_0_checked : (List.range' 1074176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2098_1_checked : (List.range' 1074304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2098_2_checked : (List.range' 1074432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2098_3_checked : (List.range' 1074560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2098_range (index : Nat) (lower : 1074176 ≤ index) (upper : index < 1074688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1074432 then
    if cut : index < 1074304 then
      exact segment_sound _ 1074176 128 Restriction2098_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1074304 128 Restriction2098_1_checked index (by omega) (by omega)
  else
    if cut : index < 1074560 then
      exact segment_sound _ 1074432 128 Restriction2098_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1074560 128 Restriction2098_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
