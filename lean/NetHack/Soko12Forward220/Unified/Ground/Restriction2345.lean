import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2345_0_checked : (List.range' 1200640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2345_1_checked : (List.range' 1200768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2345_2_checked : (List.range' 1200896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2345_3_checked : (List.range' 1201024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2345_range (index : Nat) (lower : 1200640 ≤ index) (upper : index < 1201152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1200896 then
    if cut : index < 1200768 then
      exact segment_sound _ 1200640 128 Restriction2345_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1200768 128 Restriction2345_1_checked index (by omega) (by omega)
  else
    if cut : index < 1201024 then
      exact segment_sound _ 1200896 128 Restriction2345_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1201024 128 Restriction2345_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
