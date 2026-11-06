import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1951_0_checked : (List.range' 998912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1951_1_checked : (List.range' 999040 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1951_2_checked : (List.range' 999168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1951_3_checked : (List.range' 999296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1951_range (index : Nat) (lower : 998912 ≤ index) (upper : index < 999424) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 999168 then
    if cut : index < 999040 then
      exact segment_sound _ 998912 128 Restriction1951_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 999040 128 Restriction1951_1_checked index (by omega) (by omega)
  else
    if cut : index < 999296 then
      exact segment_sound _ 999168 128 Restriction1951_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 999296 128 Restriction1951_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
