import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2267_0_checked : (List.range' 1160704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2267_1_checked : (List.range' 1160832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2267_2_checked : (List.range' 1160960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2267_3_checked : (List.range' 1161088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2267_range (index : Nat) (lower : 1160704 ≤ index) (upper : index < 1161216) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1160960 then
    if cut : index < 1160832 then
      exact segment_sound _ 1160704 128 Restriction2267_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1160832 128 Restriction2267_1_checked index (by omega) (by omega)
  else
    if cut : index < 1161088 then
      exact segment_sound _ 1160960 128 Restriction2267_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1161088 128 Restriction2267_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
