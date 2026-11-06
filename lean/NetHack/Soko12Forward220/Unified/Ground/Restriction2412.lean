import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2412_0_checked : (List.range' 1234944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2412_1_checked : (List.range' 1235072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2412_2_checked : (List.range' 1235200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2412_3_checked : (List.range' 1235328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2412_range (index : Nat) (lower : 1234944 ≤ index) (upper : index < 1235456) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1235200 then
    if cut : index < 1235072 then
      exact segment_sound _ 1234944 128 Restriction2412_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1235072 128 Restriction2412_1_checked index (by omega) (by omega)
  else
    if cut : index < 1235328 then
      exact segment_sound _ 1235200 128 Restriction2412_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1235328 128 Restriction2412_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
