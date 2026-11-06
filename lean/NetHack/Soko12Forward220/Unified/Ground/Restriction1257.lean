import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1257_0_checked : (List.range' 643584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1257_1_checked : (List.range' 643712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1257_2_checked : (List.range' 643840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1257_3_checked : (List.range' 643968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1257_range (index : Nat) (lower : 643584 ≤ index) (upper : index < 644096) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 643840 then
    if cut : index < 643712 then
      exact segment_sound _ 643584 128 Restriction1257_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 643712 128 Restriction1257_1_checked index (by omega) (by omega)
  else
    if cut : index < 643968 then
      exact segment_sound _ 643840 128 Restriction1257_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 643968 128 Restriction1257_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
