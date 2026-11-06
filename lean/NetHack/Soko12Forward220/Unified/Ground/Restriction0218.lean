import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0218_0_checked : (List.range' 111616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0218_1_checked : (List.range' 111744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0218_2_checked : (List.range' 111872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0218_3_checked : (List.range' 112000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0218_range (index : Nat) (lower : 111616 ≤ index) (upper : index < 112128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 111872 then
    if cut : index < 111744 then
      exact segment_sound _ 111616 128 Restriction0218_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 111744 128 Restriction0218_1_checked index (by omega) (by omega)
  else
    if cut : index < 112000 then
      exact segment_sound _ 111872 128 Restriction0218_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 112000 128 Restriction0218_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
