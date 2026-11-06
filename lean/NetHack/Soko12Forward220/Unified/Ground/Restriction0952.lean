import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0952_0_checked : (List.range' 487424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0952_1_checked : (List.range' 487552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0952_2_checked : (List.range' 487680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0952_3_checked : (List.range' 487808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0952_range (index : Nat) (lower : 487424 ≤ index) (upper : index < 487936) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 487680 then
    if cut : index < 487552 then
      exact segment_sound _ 487424 128 Restriction0952_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 487552 128 Restriction0952_1_checked index (by omega) (by omega)
  else
    if cut : index < 487808 then
      exact segment_sound _ 487680 128 Restriction0952_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 487808 128 Restriction0952_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
