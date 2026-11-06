import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2429_0_checked : (List.range' 1243648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2429_1_checked : (List.range' 1243776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2429_2_checked : (List.range' 1243904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2429_3_checked : (List.range' 1244032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2429_range (index : Nat) (lower : 1243648 ≤ index) (upper : index < 1244160) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1243904 then
    if cut : index < 1243776 then
      exact segment_sound _ 1243648 128 Restriction2429_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1243776 128 Restriction2429_1_checked index (by omega) (by omega)
  else
    if cut : index < 1244032 then
      exact segment_sound _ 1243904 128 Restriction2429_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1244032 128 Restriction2429_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
