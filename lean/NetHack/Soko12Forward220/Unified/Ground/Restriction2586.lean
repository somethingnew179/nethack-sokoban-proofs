import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2586_0_checked : (List.range' 1324032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2586_1_checked : (List.range' 1324160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2586_2_checked : (List.range' 1324288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2586_3_checked : (List.range' 1324416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2586_range (index : Nat) (lower : 1324032 ≤ index) (upper : index < 1324544) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1324288 then
    if cut : index < 1324160 then
      exact segment_sound _ 1324032 128 Restriction2586_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1324160 128 Restriction2586_1_checked index (by omega) (by omega)
  else
    if cut : index < 1324416 then
      exact segment_sound _ 1324288 128 Restriction2586_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1324416 128 Restriction2586_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
