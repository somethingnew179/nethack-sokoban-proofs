import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0573_0_checked : (List.range' 293376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0573_1_checked : (List.range' 293504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0573_2_checked : (List.range' 293632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0573_3_checked : (List.range' 293760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0573_range (index : Nat) (lower : 293376 ≤ index) (upper : index < 293888) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 293632 then
    if cut : index < 293504 then
      exact segment_sound _ 293376 128 Restriction0573_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 293504 128 Restriction0573_1_checked index (by omega) (by omega)
  else
    if cut : index < 293760 then
      exact segment_sound _ 293632 128 Restriction0573_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 293760 128 Restriction0573_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
