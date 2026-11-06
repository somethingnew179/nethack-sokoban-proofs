import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0833_0_checked : (List.range' 426496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0833_1_checked : (List.range' 426624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0833_2_checked : (List.range' 426752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0833_3_checked : (List.range' 426880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0833_range (index : Nat) (lower : 426496 ≤ index) (upper : index < 427008) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 426752 then
    if cut : index < 426624 then
      exact segment_sound _ 426496 128 Restriction0833_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 426624 128 Restriction0833_1_checked index (by omega) (by omega)
  else
    if cut : index < 426880 then
      exact segment_sound _ 426752 128 Restriction0833_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 426880 128 Restriction0833_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
