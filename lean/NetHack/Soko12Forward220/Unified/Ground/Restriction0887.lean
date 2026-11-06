import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0887_0_checked : (List.range' 454144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0887_1_checked : (List.range' 454272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0887_2_checked : (List.range' 454400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0887_3_checked : (List.range' 454528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0887_range (index : Nat) (lower : 454144 ≤ index) (upper : index < 454656) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 454400 then
    if cut : index < 454272 then
      exact segment_sound _ 454144 128 Restriction0887_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 454272 128 Restriction0887_1_checked index (by omega) (by omega)
  else
    if cut : index < 454528 then
      exact segment_sound _ 454400 128 Restriction0887_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 454528 128 Restriction0887_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
