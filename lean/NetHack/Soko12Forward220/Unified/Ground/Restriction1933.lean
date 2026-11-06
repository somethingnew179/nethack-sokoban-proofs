import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1933_0_checked : (List.range' 989696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1933_1_checked : (List.range' 989824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1933_2_checked : (List.range' 989952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1933_3_checked : (List.range' 990080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1933_range (index : Nat) (lower : 989696 ≤ index) (upper : index < 990208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 989952 then
    if cut : index < 989824 then
      exact segment_sound _ 989696 128 Restriction1933_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 989824 128 Restriction1933_1_checked index (by omega) (by omega)
  else
    if cut : index < 990080 then
      exact segment_sound _ 989952 128 Restriction1933_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 990080 128 Restriction1933_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
