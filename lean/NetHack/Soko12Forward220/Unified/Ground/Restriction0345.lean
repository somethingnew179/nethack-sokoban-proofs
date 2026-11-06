import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0345_0_checked : (List.range' 176640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0345_1_checked : (List.range' 176768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0345_2_checked : (List.range' 176896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0345_3_checked : (List.range' 177024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0345_range (index : Nat) (lower : 176640 ≤ index) (upper : index < 177152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 176896 then
    if cut : index < 176768 then
      exact segment_sound _ 176640 128 Restriction0345_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 176768 128 Restriction0345_1_checked index (by omega) (by omega)
  else
    if cut : index < 177024 then
      exact segment_sound _ 176896 128 Restriction0345_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 177024 128 Restriction0345_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
