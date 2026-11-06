import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0423_0_checked : (List.range' 216576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0423_1_checked : (List.range' 216704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0423_2_checked : (List.range' 216832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0423_3_checked : (List.range' 216960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0423_range (index : Nat) (lower : 216576 ≤ index) (upper : index < 217088) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 216832 then
    if cut : index < 216704 then
      exact segment_sound _ 216576 128 Restriction0423_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 216704 128 Restriction0423_1_checked index (by omega) (by omega)
  else
    if cut : index < 216960 then
      exact segment_sound _ 216832 128 Restriction0423_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 216960 128 Restriction0423_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
