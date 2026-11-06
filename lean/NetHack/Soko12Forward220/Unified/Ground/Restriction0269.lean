import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0269_0_checked : (List.range' 137728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0269_1_checked : (List.range' 137856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0269_2_checked : (List.range' 137984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0269_3_checked : (List.range' 138112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0269_range (index : Nat) (lower : 137728 ≤ index) (upper : index < 138240) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 137984 then
    if cut : index < 137856 then
      exact segment_sound _ 137728 128 Restriction0269_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 137856 128 Restriction0269_1_checked index (by omega) (by omega)
  else
    if cut : index < 138112 then
      exact segment_sound _ 137984 128 Restriction0269_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 138112 128 Restriction0269_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
