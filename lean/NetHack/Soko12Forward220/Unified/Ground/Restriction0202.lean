import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0202_0_checked : (List.range' 103424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0202_1_checked : (List.range' 103552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0202_2_checked : (List.range' 103680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0202_3_checked : (List.range' 103808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0202_range (index : Nat) (lower : 103424 ≤ index) (upper : index < 103936) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 103680 then
    if cut : index < 103552 then
      exact segment_sound _ 103424 128 Restriction0202_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 103552 128 Restriction0202_1_checked index (by omega) (by omega)
  else
    if cut : index < 103808 then
      exact segment_sound _ 103680 128 Restriction0202_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 103808 128 Restriction0202_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
