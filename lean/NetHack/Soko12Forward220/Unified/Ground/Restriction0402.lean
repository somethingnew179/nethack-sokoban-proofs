import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0402_0_checked : (List.range' 205824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0402_1_checked : (List.range' 205952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0402_2_checked : (List.range' 206080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0402_3_checked : (List.range' 206208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0402_range (index : Nat) (lower : 205824 ≤ index) (upper : index < 206336) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 206080 then
    if cut : index < 205952 then
      exact segment_sound _ 205824 128 Restriction0402_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 205952 128 Restriction0402_1_checked index (by omega) (by omega)
  else
    if cut : index < 206208 then
      exact segment_sound _ 206080 128 Restriction0402_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 206208 128 Restriction0402_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
