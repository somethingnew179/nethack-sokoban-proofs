import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2258_0_checked : (List.range' 1156096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2258_1_checked : (List.range' 1156224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2258_2_checked : (List.range' 1156352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2258_3_checked : (List.range' 1156480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2258_range (index : Nat) (lower : 1156096 ≤ index) (upper : index < 1156608) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1156352 then
    if cut : index < 1156224 then
      exact segment_sound _ 1156096 128 Restriction2258_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1156224 128 Restriction2258_1_checked index (by omega) (by omega)
  else
    if cut : index < 1156480 then
      exact segment_sound _ 1156352 128 Restriction2258_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1156480 128 Restriction2258_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
