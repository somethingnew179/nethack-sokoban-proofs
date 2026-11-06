import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1882_0_checked : (List.range' 963584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1882_1_checked : (List.range' 963712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1882_2_checked : (List.range' 963840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1882_3_checked : (List.range' 963968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1882_range (index : Nat) (lower : 963584 ≤ index) (upper : index < 964096) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 963840 then
    if cut : index < 963712 then
      exact segment_sound _ 963584 128 Restriction1882_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 963712 128 Restriction1882_1_checked index (by omega) (by omega)
  else
    if cut : index < 963968 then
      exact segment_sound _ 963840 128 Restriction1882_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 963968 128 Restriction1882_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
