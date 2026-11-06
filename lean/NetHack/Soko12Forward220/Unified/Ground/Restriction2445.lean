import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2445_0_checked : (List.range' 1251840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2445_1_checked : (List.range' 1251968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2445_2_checked : (List.range' 1252096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2445_3_checked : (List.range' 1252224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2445_range (index : Nat) (lower : 1251840 ≤ index) (upper : index < 1252352) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1252096 then
    if cut : index < 1251968 then
      exact segment_sound _ 1251840 128 Restriction2445_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1251968 128 Restriction2445_1_checked index (by omega) (by omega)
  else
    if cut : index < 1252224 then
      exact segment_sound _ 1252096 128 Restriction2445_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1252224 128 Restriction2445_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
