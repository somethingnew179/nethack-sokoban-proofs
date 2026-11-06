import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1256_0_checked : (List.range' 643072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1256_1_checked : (List.range' 643200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1256_2_checked : (List.range' 643328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1256_3_checked : (List.range' 643456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1256_range (index : Nat) (lower : 643072 ≤ index) (upper : index < 643584) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 643328 then
    if cut : index < 643200 then
      exact segment_sound _ 643072 128 Restriction1256_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 643200 128 Restriction1256_1_checked index (by omega) (by omega)
  else
    if cut : index < 643456 then
      exact segment_sound _ 643328 128 Restriction1256_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 643456 128 Restriction1256_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
