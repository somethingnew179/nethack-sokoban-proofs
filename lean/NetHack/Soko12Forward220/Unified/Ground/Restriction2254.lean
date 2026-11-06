import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2254_0_checked : (List.range' 1154048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2254_1_checked : (List.range' 1154176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2254_2_checked : (List.range' 1154304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2254_3_checked : (List.range' 1154432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2254_range (index : Nat) (lower : 1154048 ≤ index) (upper : index < 1154560) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1154304 then
    if cut : index < 1154176 then
      exact segment_sound _ 1154048 128 Restriction2254_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1154176 128 Restriction2254_1_checked index (by omega) (by omega)
  else
    if cut : index < 1154432 then
      exact segment_sound _ 1154304 128 Restriction2254_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1154432 128 Restriction2254_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
