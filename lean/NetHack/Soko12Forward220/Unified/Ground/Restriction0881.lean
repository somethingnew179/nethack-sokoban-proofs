import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0881_0_checked : (List.range' 451072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0881_1_checked : (List.range' 451200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0881_2_checked : (List.range' 451328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0881_3_checked : (List.range' 451456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0881_range (index : Nat) (lower : 451072 ≤ index) (upper : index < 451584) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 451328 then
    if cut : index < 451200 then
      exact segment_sound _ 451072 128 Restriction0881_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 451200 128 Restriction0881_1_checked index (by omega) (by omega)
  else
    if cut : index < 451456 then
      exact segment_sound _ 451328 128 Restriction0881_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 451456 128 Restriction0881_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
