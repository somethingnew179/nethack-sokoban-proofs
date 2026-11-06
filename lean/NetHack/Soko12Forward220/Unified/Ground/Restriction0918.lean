import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0918_0_checked : (List.range' 470016 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0918_1_checked : (List.range' 470144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0918_2_checked : (List.range' 470272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0918_3_checked : (List.range' 470400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0918_range (index : Nat) (lower : 470016 ≤ index) (upper : index < 470528) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 470272 then
    if cut : index < 470144 then
      exact segment_sound _ 470016 128 Restriction0918_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 470144 128 Restriction0918_1_checked index (by omega) (by omega)
  else
    if cut : index < 470400 then
      exact segment_sound _ 470272 128 Restriction0918_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 470400 128 Restriction0918_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
