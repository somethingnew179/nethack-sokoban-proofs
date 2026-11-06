import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0675_0_checked : (List.range' 345600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0675_1_checked : (List.range' 345728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0675_2_checked : (List.range' 345856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0675_3_checked : (List.range' 345984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0675_range (index : Nat) (lower : 345600 ≤ index) (upper : index < 346112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 345856 then
    if cut : index < 345728 then
      exact segment_sound _ 345600 128 Restriction0675_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 345728 128 Restriction0675_1_checked index (by omega) (by omega)
  else
    if cut : index < 345984 then
      exact segment_sound _ 345856 128 Restriction0675_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 345984 128 Restriction0675_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
