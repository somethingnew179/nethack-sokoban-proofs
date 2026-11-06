import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0387_0_checked : (List.range' 198144 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0387_1_checked : (List.range' 198272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0387_2_checked : (List.range' 198400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0387_3_checked : (List.range' 198528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0387_range (index : Nat) (lower : 198144 ≤ index) (upper : index < 198656) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 198400 then
    if cut : index < 198272 then
      exact segment_sound _ 198144 128 Restriction0387_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 198272 128 Restriction0387_1_checked index (by omega) (by omega)
  else
    if cut : index < 198528 then
      exact segment_sound _ 198400 128 Restriction0387_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 198528 128 Restriction0387_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
