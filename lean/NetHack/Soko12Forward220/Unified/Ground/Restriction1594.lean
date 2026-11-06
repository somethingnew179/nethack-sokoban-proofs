import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1594_0_checked : (List.range' 816128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1594_1_checked : (List.range' 816256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1594_2_checked : (List.range' 816384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1594_3_checked : (List.range' 816512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1594_range (index : Nat) (lower : 816128 ≤ index) (upper : index < 816640) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 816384 then
    if cut : index < 816256 then
      exact segment_sound _ 816128 128 Restriction1594_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 816256 128 Restriction1594_1_checked index (by omega) (by omega)
  else
    if cut : index < 816512 then
      exact segment_sound _ 816384 128 Restriction1594_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 816512 128 Restriction1594_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
