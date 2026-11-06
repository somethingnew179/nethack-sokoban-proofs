import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0127_0_checked : (List.range' 65024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0127_1_checked : (List.range' 65152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0127_2_checked : (List.range' 65280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0127_3_checked : (List.range' 65408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0127_range (index : Nat) (lower : 65024 ≤ index) (upper : index < 65536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 65280 then
    if cut : index < 65152 then
      exact segment_sound _ 65024 128 Restriction0127_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 65152 128 Restriction0127_1_checked index (by omega) (by omega)
  else
    if cut : index < 65408 then
      exact segment_sound _ 65280 128 Restriction0127_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 65408 128 Restriction0127_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
