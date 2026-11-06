import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2241_0_checked : (List.range' 1147392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2241_1_checked : (List.range' 1147520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2241_2_checked : (List.range' 1147648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2241_3_checked : (List.range' 1147776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2241_range (index : Nat) (lower : 1147392 ≤ index) (upper : index < 1147904) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1147648 then
    if cut : index < 1147520 then
      exact segment_sound _ 1147392 128 Restriction2241_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1147520 128 Restriction2241_1_checked index (by omega) (by omega)
  else
    if cut : index < 1147776 then
      exact segment_sound _ 1147648 128 Restriction2241_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1147776 128 Restriction2241_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
