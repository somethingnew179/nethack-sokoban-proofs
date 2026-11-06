import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1634_0_checked : (List.range' 836608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1634_1_checked : (List.range' 836736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1634_2_checked : (List.range' 836864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1634_3_checked : (List.range' 836992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1634_range (index : Nat) (lower : 836608 ≤ index) (upper : index < 837120) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 836864 then
    if cut : index < 836736 then
      exact segment_sound _ 836608 128 Restriction1634_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 836736 128 Restriction1634_1_checked index (by omega) (by omega)
  else
    if cut : index < 836992 then
      exact segment_sound _ 836864 128 Restriction1634_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 836992 128 Restriction1634_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
