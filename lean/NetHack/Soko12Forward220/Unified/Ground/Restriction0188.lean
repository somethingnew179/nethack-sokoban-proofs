import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0188_0_checked : (List.range' 96256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0188_1_checked : (List.range' 96384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0188_2_checked : (List.range' 96512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0188_3_checked : (List.range' 96640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0188_range (index : Nat) (lower : 96256 ≤ index) (upper : index < 96768) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 96512 then
    if cut : index < 96384 then
      exact segment_sound _ 96256 128 Restriction0188_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 96384 128 Restriction0188_1_checked index (by omega) (by omega)
  else
    if cut : index < 96640 then
      exact segment_sound _ 96512 128 Restriction0188_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 96640 128 Restriction0188_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
