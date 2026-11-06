import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0014_0_checked : (List.range' 7168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0014_1_checked : (List.range' 7296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0014_2_checked : (List.range' 7424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0014_3_checked : (List.range' 7552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0014_range (index : Nat) (lower : 7168 ≤ index) (upper : index < 7680) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 7424 then
    if cut : index < 7296 then
      exact segment_sound _ 7168 128 Restriction0014_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 7296 128 Restriction0014_1_checked index (by omega) (by omega)
  else
    if cut : index < 7552 then
      exact segment_sound _ 7424 128 Restriction0014_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 7552 128 Restriction0014_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
