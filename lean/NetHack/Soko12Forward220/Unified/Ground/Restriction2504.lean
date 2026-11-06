import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2504_0_checked : (List.range' 1282048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2504_1_checked : (List.range' 1282176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2504_2_checked : (List.range' 1282304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2504_3_checked : (List.range' 1282432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2504_range (index : Nat) (lower : 1282048 ≤ index) (upper : index < 1282560) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1282304 then
    if cut : index < 1282176 then
      exact segment_sound _ 1282048 128 Restriction2504_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1282176 128 Restriction2504_1_checked index (by omega) (by omega)
  else
    if cut : index < 1282432 then
      exact segment_sound _ 1282304 128 Restriction2504_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1282432 128 Restriction2504_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
