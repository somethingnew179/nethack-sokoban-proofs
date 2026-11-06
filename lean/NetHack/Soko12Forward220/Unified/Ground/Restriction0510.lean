import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0510_0_checked : (List.range' 261120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0510_1_checked : (List.range' 261248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0510_2_checked : (List.range' 261376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0510_3_checked : (List.range' 261504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0510_range (index : Nat) (lower : 261120 ≤ index) (upper : index < 261632) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 261376 then
    if cut : index < 261248 then
      exact segment_sound _ 261120 128 Restriction0510_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 261248 128 Restriction0510_1_checked index (by omega) (by omega)
  else
    if cut : index < 261504 then
      exact segment_sound _ 261376 128 Restriction0510_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 261504 128 Restriction0510_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
