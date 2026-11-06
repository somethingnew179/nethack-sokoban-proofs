import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0600_0_checked : (List.range' 307200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0600_1_checked : (List.range' 307328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0600_2_checked : (List.range' 307456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0600_3_checked : (List.range' 307584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0600_range (index : Nat) (lower : 307200 ≤ index) (upper : index < 307712) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 307456 then
    if cut : index < 307328 then
      exact segment_sound _ 307200 128 Restriction0600_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 307328 128 Restriction0600_1_checked index (by omega) (by omega)
  else
    if cut : index < 307584 then
      exact segment_sound _ 307456 128 Restriction0600_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 307584 128 Restriction0600_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
