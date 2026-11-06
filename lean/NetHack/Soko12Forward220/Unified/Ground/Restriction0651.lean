import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0651_0_checked : (List.range' 333312 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0651_1_checked : (List.range' 333440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0651_2_checked : (List.range' 333568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0651_3_checked : (List.range' 333696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0651_range (index : Nat) (lower : 333312 ≤ index) (upper : index < 333824) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 333568 then
    if cut : index < 333440 then
      exact segment_sound _ 333312 128 Restriction0651_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 333440 128 Restriction0651_1_checked index (by omega) (by omega)
  else
    if cut : index < 333696 then
      exact segment_sound _ 333568 128 Restriction0651_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 333696 128 Restriction0651_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
