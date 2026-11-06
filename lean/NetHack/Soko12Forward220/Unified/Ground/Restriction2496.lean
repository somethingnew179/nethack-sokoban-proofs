import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2496_0_checked : (List.range' 1277952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2496_1_checked : (List.range' 1278080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2496_2_checked : (List.range' 1278208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2496_3_checked : (List.range' 1278336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2496_range (index : Nat) (lower : 1277952 ≤ index) (upper : index < 1278464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1278208 then
    if cut : index < 1278080 then
      exact segment_sound _ 1277952 128 Restriction2496_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1278080 128 Restriction2496_1_checked index (by omega) (by omega)
  else
    if cut : index < 1278336 then
      exact segment_sound _ 1278208 128 Restriction2496_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1278336 128 Restriction2496_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
