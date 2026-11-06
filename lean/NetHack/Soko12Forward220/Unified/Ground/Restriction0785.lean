import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0785_0_checked : (List.range' 401920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0785_1_checked : (List.range' 402048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0785_2_checked : (List.range' 402176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0785_3_checked : (List.range' 402304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0785_range (index : Nat) (lower : 401920 ≤ index) (upper : index < 402432) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 402176 then
    if cut : index < 402048 then
      exact segment_sound _ 401920 128 Restriction0785_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 402048 128 Restriction0785_1_checked index (by omega) (by omega)
  else
    if cut : index < 402304 then
      exact segment_sound _ 402176 128 Restriction0785_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 402304 128 Restriction0785_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
