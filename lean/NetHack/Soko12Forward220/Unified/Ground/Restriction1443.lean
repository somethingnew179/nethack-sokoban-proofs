import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1443_0_checked : (List.range' 738816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1443_1_checked : (List.range' 738944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1443_2_checked : (List.range' 739072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1443_3_checked : (List.range' 739200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1443_range (index : Nat) (lower : 738816 ≤ index) (upper : index < 739328) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 739072 then
    if cut : index < 738944 then
      exact segment_sound _ 738816 128 Restriction1443_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 738944 128 Restriction1443_1_checked index (by omega) (by omega)
  else
    if cut : index < 739200 then
      exact segment_sound _ 739072 128 Restriction1443_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 739200 128 Restriction1443_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
