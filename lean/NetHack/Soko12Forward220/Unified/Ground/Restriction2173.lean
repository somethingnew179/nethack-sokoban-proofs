import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2173_0_checked : (List.range' 1112576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2173_1_checked : (List.range' 1112704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2173_2_checked : (List.range' 1112832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2173_3_checked : (List.range' 1112960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2173_range (index : Nat) (lower : 1112576 ≤ index) (upper : index < 1113088) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1112832 then
    if cut : index < 1112704 then
      exact segment_sound _ 1112576 128 Restriction2173_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1112704 128 Restriction2173_1_checked index (by omega) (by omega)
  else
    if cut : index < 1112960 then
      exact segment_sound _ 1112832 128 Restriction2173_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1112960 128 Restriction2173_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
