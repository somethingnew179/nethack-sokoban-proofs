import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0502_0_checked : (List.range' 257024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0502_1_checked : (List.range' 257152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0502_2_checked : (List.range' 257280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0502_3_checked : (List.range' 257408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0502_range (index : Nat) (lower : 257024 ≤ index) (upper : index < 257536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 257280 then
    if cut : index < 257152 then
      exact segment_sound _ 257024 128 Restriction0502_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 257152 128 Restriction0502_1_checked index (by omega) (by omega)
  else
    if cut : index < 257408 then
      exact segment_sound _ 257280 128 Restriction0502_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 257408 128 Restriction0502_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
