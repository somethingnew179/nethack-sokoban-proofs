import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0199_0_checked : (List.range' 101888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0199_1_checked : (List.range' 102016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0199_2_checked : (List.range' 102144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0199_3_checked : (List.range' 102272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0199_range (index : Nat) (lower : 101888 ≤ index) (upper : index < 102400) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 102144 then
    if cut : index < 102016 then
      exact segment_sound _ 101888 128 Restriction0199_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 102016 128 Restriction0199_1_checked index (by omega) (by omega)
  else
    if cut : index < 102272 then
      exact segment_sound _ 102144 128 Restriction0199_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 102272 128 Restriction0199_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
