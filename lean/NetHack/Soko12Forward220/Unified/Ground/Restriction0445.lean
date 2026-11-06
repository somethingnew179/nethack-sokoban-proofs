import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0445_0_checked : (List.range' 227840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0445_1_checked : (List.range' 227968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0445_2_checked : (List.range' 228096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0445_3_checked : (List.range' 228224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0445_range (index : Nat) (lower : 227840 ≤ index) (upper : index < 228352) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 228096 then
    if cut : index < 227968 then
      exact segment_sound _ 227840 128 Restriction0445_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 227968 128 Restriction0445_1_checked index (by omega) (by omega)
  else
    if cut : index < 228224 then
      exact segment_sound _ 228096 128 Restriction0445_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 228224 128 Restriction0445_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
