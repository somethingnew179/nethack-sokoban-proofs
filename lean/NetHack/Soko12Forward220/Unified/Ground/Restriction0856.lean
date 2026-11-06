import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0856_0_checked : (List.range' 438272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0856_1_checked : (List.range' 438400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0856_2_checked : (List.range' 438528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0856_3_checked : (List.range' 438656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0856_range (index : Nat) (lower : 438272 ≤ index) (upper : index < 438784) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 438528 then
    if cut : index < 438400 then
      exact segment_sound _ 438272 128 Restriction0856_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 438400 128 Restriction0856_1_checked index (by omega) (by omega)
  else
    if cut : index < 438656 then
      exact segment_sound _ 438528 128 Restriction0856_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 438656 128 Restriction0856_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
