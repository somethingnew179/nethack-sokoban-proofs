import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2435_0_checked : (List.range' 1246720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2435_1_checked : (List.range' 1246848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2435_2_checked : (List.range' 1246976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2435_3_checked : (List.range' 1247104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2435_range (index : Nat) (lower : 1246720 ≤ index) (upper : index < 1247232) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1246976 then
    if cut : index < 1246848 then
      exact segment_sound _ 1246720 128 Restriction2435_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1246848 128 Restriction2435_1_checked index (by omega) (by omega)
  else
    if cut : index < 1247104 then
      exact segment_sound _ 1246976 128 Restriction2435_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1247104 128 Restriction2435_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
