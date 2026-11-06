import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0907_0_checked : (List.range' 464384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0907_1_checked : (List.range' 464512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0907_2_checked : (List.range' 464640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0907_3_checked : (List.range' 464768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0907_range (index : Nat) (lower : 464384 ≤ index) (upper : index < 464896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 464640 then
    if cut : index < 464512 then
      exact segment_sound _ 464384 128 Restriction0907_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 464512 128 Restriction0907_1_checked index (by omega) (by omega)
  else
    if cut : index < 464768 then
      exact segment_sound _ 464640 128 Restriction0907_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 464768 128 Restriction0907_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
