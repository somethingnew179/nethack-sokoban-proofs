import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0871_0_checked : (List.range' 445952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0871_1_checked : (List.range' 446080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0871_2_checked : (List.range' 446208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0871_3_checked : (List.range' 446336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0871_range (index : Nat) (lower : 445952 ≤ index) (upper : index < 446464) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 446208 then
    if cut : index < 446080 then
      exact segment_sound _ 445952 128 Restriction0871_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 446080 128 Restriction0871_1_checked index (by omega) (by omega)
  else
    if cut : index < 446336 then
      exact segment_sound _ 446208 128 Restriction0871_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 446336 128 Restriction0871_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
