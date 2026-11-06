import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2528_0_checked : (List.range' 1294336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2528_1_checked : (List.range' 1294464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2528_2_checked : (List.range' 1294592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2528_3_checked : (List.range' 1294720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2528_range (index : Nat) (lower : 1294336 ≤ index) (upper : index < 1294848) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1294592 then
    if cut : index < 1294464 then
      exact segment_sound _ 1294336 128 Restriction2528_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1294464 128 Restriction2528_1_checked index (by omega) (by omega)
  else
    if cut : index < 1294720 then
      exact segment_sound _ 1294592 128 Restriction2528_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1294720 128 Restriction2528_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
