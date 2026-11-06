import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1236_0_checked : (List.range' 632832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1236_1_checked : (List.range' 632960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1236_2_checked : (List.range' 633088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1236_3_checked : (List.range' 633216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1236_range (index : Nat) (lower : 632832 ≤ index) (upper : index < 633344) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 633088 then
    if cut : index < 632960 then
      exact segment_sound _ 632832 128 Restriction1236_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 632960 128 Restriction1236_1_checked index (by omega) (by omega)
  else
    if cut : index < 633216 then
      exact segment_sound _ 633088 128 Restriction1236_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 633216 128 Restriction1236_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
