import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0866_0_checked : (List.range' 443392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0866_1_checked : (List.range' 443520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0866_2_checked : (List.range' 443648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0866_3_checked : (List.range' 443776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0866_range (index : Nat) (lower : 443392 ≤ index) (upper : index < 443904) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 443648 then
    if cut : index < 443520 then
      exact segment_sound _ 443392 128 Restriction0866_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 443520 128 Restriction0866_1_checked index (by omega) (by omega)
  else
    if cut : index < 443776 then
      exact segment_sound _ 443648 128 Restriction0866_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 443776 128 Restriction0866_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
