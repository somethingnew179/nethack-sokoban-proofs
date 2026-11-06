import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2542_0_checked : (List.range' 1301504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2542_1_checked : (List.range' 1301632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2542_2_checked : (List.range' 1301760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2542_3_checked : (List.range' 1301888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2542_range (index : Nat) (lower : 1301504 ≤ index) (upper : index < 1302016) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1301760 then
    if cut : index < 1301632 then
      exact segment_sound _ 1301504 128 Restriction2542_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1301632 128 Restriction2542_1_checked index (by omega) (by omega)
  else
    if cut : index < 1301888 then
      exact segment_sound _ 1301760 128 Restriction2542_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1301888 128 Restriction2542_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
