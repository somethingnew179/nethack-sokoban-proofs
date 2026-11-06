import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0323_0_checked : (List.range' 165376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0323_1_checked : (List.range' 165504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0323_2_checked : (List.range' 165632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0323_3_checked : (List.range' 165760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0323_range (index : Nat) (lower : 165376 ≤ index) (upper : index < 165888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 165632 then
    if cut : index < 165504 then
      exact segment_sound _ 165376 128 Restriction0323_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 165504 128 Restriction0323_1_checked index (by omega) (by omega)
  else
    if cut : index < 165760 then
      exact segment_sound _ 165632 128 Restriction0323_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 165760 128 Restriction0323_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
