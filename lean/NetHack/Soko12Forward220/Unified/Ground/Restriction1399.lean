import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1399_0_checked : (List.range' 716288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1399_1_checked : (List.range' 716416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1399_2_checked : (List.range' 716544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1399_3_checked : (List.range' 716672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1399_range (index : Nat) (lower : 716288 ≤ index) (upper : index < 716800) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 716544 then
    if cut : index < 716416 then
      exact segment_sound _ 716288 128 Restriction1399_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 716416 128 Restriction1399_1_checked index (by omega) (by omega)
  else
    if cut : index < 716672 then
      exact segment_sound _ 716544 128 Restriction1399_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 716672 128 Restriction1399_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
