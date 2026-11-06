import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1719_0_checked : (List.range' 880128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1719_1_checked : (List.range' 880256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1719_2_checked : (List.range' 880384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1719_3_checked : (List.range' 880512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1719_range (index : Nat) (lower : 880128 ≤ index) (upper : index < 880640) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 880384 then
    if cut : index < 880256 then
      exact segment_sound _ 880128 128 Restriction1719_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 880256 128 Restriction1719_1_checked index (by omega) (by omega)
  else
    if cut : index < 880512 then
      exact segment_sound _ 880384 128 Restriction1719_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 880512 128 Restriction1719_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
