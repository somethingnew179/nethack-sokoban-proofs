import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1721_0_checked : (List.range' 881152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1721_1_checked : (List.range' 881280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1721_2_checked : (List.range' 881408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1721_3_checked : (List.range' 881536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1721_range (index : Nat) (lower : 881152 ≤ index) (upper : index < 881664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 881408 then
    if cut : index < 881280 then
      exact segment_sound _ 881152 128 Restriction1721_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 881280 128 Restriction1721_1_checked index (by omega) (by omega)
  else
    if cut : index < 881536 then
      exact segment_sound _ 881408 128 Restriction1721_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 881536 128 Restriction1721_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
