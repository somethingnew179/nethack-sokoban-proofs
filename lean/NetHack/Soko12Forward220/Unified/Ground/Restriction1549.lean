import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1549_0_checked : (List.range' 793088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1549_1_checked : (List.range' 793216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1549_2_checked : (List.range' 793344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1549_3_checked : (List.range' 793472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1549_range (index : Nat) (lower : 793088 ≤ index) (upper : index < 793600) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 793344 then
    if cut : index < 793216 then
      exact segment_sound _ 793088 128 Restriction1549_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 793216 128 Restriction1549_1_checked index (by omega) (by omega)
  else
    if cut : index < 793472 then
      exact segment_sound _ 793344 128 Restriction1549_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 793472 128 Restriction1549_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
