import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0889_0_checked : (List.range' 455168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0889_1_checked : (List.range' 455296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0889_2_checked : (List.range' 455424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0889_3_checked : (List.range' 455552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0889_range (index : Nat) (lower : 455168 ≤ index) (upper : index < 455680) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 455424 then
    if cut : index < 455296 then
      exact segment_sound _ 455168 128 Restriction0889_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 455296 128 Restriction0889_1_checked index (by omega) (by omega)
  else
    if cut : index < 455552 then
      exact segment_sound _ 455424 128 Restriction0889_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 455552 128 Restriction0889_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
