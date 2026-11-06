import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1507_0_checked : (List.range' 771584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1507_1_checked : (List.range' 771712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1507_2_checked : (List.range' 771840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1507_3_checked : (List.range' 771968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1507_range (index : Nat) (lower : 771584 ≤ index) (upper : index < 772096) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 771840 then
    if cut : index < 771712 then
      exact segment_sound _ 771584 128 Restriction1507_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 771712 128 Restriction1507_1_checked index (by omega) (by omega)
  else
    if cut : index < 771968 then
      exact segment_sound _ 771840 128 Restriction1507_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 771968 128 Restriction1507_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
