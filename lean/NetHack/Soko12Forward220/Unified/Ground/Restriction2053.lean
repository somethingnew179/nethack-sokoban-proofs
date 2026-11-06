import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2053_0_checked : (List.range' 1051136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2053_1_checked : (List.range' 1051264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2053_2_checked : (List.range' 1051392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2053_3_checked : (List.range' 1051520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2053_range (index : Nat) (lower : 1051136 ≤ index) (upper : index < 1051648) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1051392 then
    if cut : index < 1051264 then
      exact segment_sound _ 1051136 128 Restriction2053_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1051264 128 Restriction2053_1_checked index (by omega) (by omega)
  else
    if cut : index < 1051520 then
      exact segment_sound _ 1051392 128 Restriction2053_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1051520 128 Restriction2053_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
