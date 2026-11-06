import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2379_0_checked : (List.range' 1218048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2379_1_checked : (List.range' 1218176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2379_2_checked : (List.range' 1218304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2379_3_checked : (List.range' 1218432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2379_range (index : Nat) (lower : 1218048 ≤ index) (upper : index < 1218560) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1218304 then
    if cut : index < 1218176 then
      exact segment_sound _ 1218048 128 Restriction2379_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1218176 128 Restriction2379_1_checked index (by omega) (by omega)
  else
    if cut : index < 1218432 then
      exact segment_sound _ 1218304 128 Restriction2379_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1218432 128 Restriction2379_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
