import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0810_0_checked : (List.range' 414720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0810_1_checked : (List.range' 414848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0810_2_checked : (List.range' 414976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0810_3_checked : (List.range' 415104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0810_range (index : Nat) (lower : 414720 ≤ index) (upper : index < 415232) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 414976 then
    if cut : index < 414848 then
      exact segment_sound _ 414720 128 Restriction0810_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 414848 128 Restriction0810_1_checked index (by omega) (by omega)
  else
    if cut : index < 415104 then
      exact segment_sound _ 414976 128 Restriction0810_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 415104 128 Restriction0810_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
