import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1762_0_checked : (List.range' 902144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1762_1_checked : (List.range' 902272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1762_2_checked : (List.range' 902400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1762_3_checked : (List.range' 902528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1762_range (index : Nat) (lower : 902144 ≤ index) (upper : index < 902656) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 902400 then
    if cut : index < 902272 then
      exact segment_sound _ 902144 128 Restriction1762_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 902272 128 Restriction1762_1_checked index (by omega) (by omega)
  else
    if cut : index < 902528 then
      exact segment_sound _ 902400 128 Restriction1762_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 902528 128 Restriction1762_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
