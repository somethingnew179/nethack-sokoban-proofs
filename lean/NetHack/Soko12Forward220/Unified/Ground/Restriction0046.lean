import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0046_0_checked : (List.range' 23552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0046_1_checked : (List.range' 23680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0046_2_checked : (List.range' 23808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0046_3_checked : (List.range' 23936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0046_range (index : Nat) (lower : 23552 ≤ index) (upper : index < 24064) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 23808 then
    if cut : index < 23680 then
      exact segment_sound _ 23552 128 Restriction0046_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 23680 128 Restriction0046_1_checked index (by omega) (by omega)
  else
    if cut : index < 23936 then
      exact segment_sound _ 23808 128 Restriction0046_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 23936 128 Restriction0046_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
