import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0599_0_checked : (List.range' 306688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0599_1_checked : (List.range' 306816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0599_2_checked : (List.range' 306944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0599_3_checked : (List.range' 307072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0599_range (index : Nat) (lower : 306688 ≤ index) (upper : index < 307200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 306944 then
    if cut : index < 306816 then
      exact segment_sound _ 306688 128 Restriction0599_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 306816 128 Restriction0599_1_checked index (by omega) (by omega)
  else
    if cut : index < 307072 then
      exact segment_sound _ 306944 128 Restriction0599_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 307072 128 Restriction0599_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
