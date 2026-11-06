import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1471_0_checked : (List.range' 753152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1471_1_checked : (List.range' 753280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1471_2_checked : (List.range' 753408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1471_3_checked : (List.range' 753536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1471_range (index : Nat) (lower : 753152 ≤ index) (upper : index < 753664) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 753408 then
    if cut : index < 753280 then
      exact segment_sound _ 753152 128 Restriction1471_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 753280 128 Restriction1471_1_checked index (by omega) (by omega)
  else
    if cut : index < 753536 then
      exact segment_sound _ 753408 128 Restriction1471_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 753536 128 Restriction1471_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
