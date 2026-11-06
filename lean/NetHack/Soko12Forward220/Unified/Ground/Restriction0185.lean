import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0185_0_checked : (List.range' 94720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0185_1_checked : (List.range' 94848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0185_2_checked : (List.range' 94976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0185_3_checked : (List.range' 95104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0185_range (index : Nat) (lower : 94720 ≤ index) (upper : index < 95232) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 94976 then
    if cut : index < 94848 then
      exact segment_sound _ 94720 128 Restriction0185_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 94848 128 Restriction0185_1_checked index (by omega) (by omega)
  else
    if cut : index < 95104 then
      exact segment_sound _ 94976 128 Restriction0185_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 95104 128 Restriction0185_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
