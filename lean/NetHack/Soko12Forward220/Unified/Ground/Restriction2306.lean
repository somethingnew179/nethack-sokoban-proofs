import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2306_0_checked : (List.range' 1180672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2306_1_checked : (List.range' 1180800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2306_2_checked : (List.range' 1180928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2306_3_checked : (List.range' 1181056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2306_range (index : Nat) (lower : 1180672 ≤ index) (upper : index < 1181184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1180928 then
    if cut : index < 1180800 then
      exact segment_sound _ 1180672 128 Restriction2306_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1180800 128 Restriction2306_1_checked index (by omega) (by omega)
  else
    if cut : index < 1181056 then
      exact segment_sound _ 1180928 128 Restriction2306_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1181056 128 Restriction2306_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
