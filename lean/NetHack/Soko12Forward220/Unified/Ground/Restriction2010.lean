import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2010_0_checked : (List.range' 1029120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2010_1_checked : (List.range' 1029248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2010_2_checked : (List.range' 1029376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2010_3_checked : (List.range' 1029504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2010_range (index : Nat) (lower : 1029120 ≤ index) (upper : index < 1029632) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1029376 then
    if cut : index < 1029248 then
      exact segment_sound _ 1029120 128 Restriction2010_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1029248 128 Restriction2010_1_checked index (by omega) (by omega)
  else
    if cut : index < 1029504 then
      exact segment_sound _ 1029376 128 Restriction2010_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1029504 128 Restriction2010_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
