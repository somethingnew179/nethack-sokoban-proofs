import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2317_0_checked : (List.range' 1186304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2317_1_checked : (List.range' 1186432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2317_2_checked : (List.range' 1186560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2317_3_checked : (List.range' 1186688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2317_range (index : Nat) (lower : 1186304 ≤ index) (upper : index < 1186816) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1186560 then
    if cut : index < 1186432 then
      exact segment_sound _ 1186304 128 Restriction2317_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1186432 128 Restriction2317_1_checked index (by omega) (by omega)
  else
    if cut : index < 1186688 then
      exact segment_sound _ 1186560 128 Restriction2317_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1186688 128 Restriction2317_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
