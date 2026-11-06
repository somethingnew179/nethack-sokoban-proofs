import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0481_0_checked : (List.range' 246272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0481_1_checked : (List.range' 246400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0481_2_checked : (List.range' 246528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0481_3_checked : (List.range' 246656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0481_range (index : Nat) (lower : 246272 ≤ index) (upper : index < 246784) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 246528 then
    if cut : index < 246400 then
      exact segment_sound _ 246272 128 Restriction0481_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 246400 128 Restriction0481_1_checked index (by omega) (by omega)
  else
    if cut : index < 246656 then
      exact segment_sound _ 246528 128 Restriction0481_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 246656 128 Restriction0481_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
