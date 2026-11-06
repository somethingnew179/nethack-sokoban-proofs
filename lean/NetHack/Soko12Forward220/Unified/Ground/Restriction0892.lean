import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0892_0_checked : (List.range' 456704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0892_1_checked : (List.range' 456832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0892_2_checked : (List.range' 456960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0892_3_checked : (List.range' 457088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0892_range (index : Nat) (lower : 456704 ≤ index) (upper : index < 457216) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 456960 then
    if cut : index < 456832 then
      exact segment_sound _ 456704 128 Restriction0892_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 456832 128 Restriction0892_1_checked index (by omega) (by omega)
  else
    if cut : index < 457088 then
      exact segment_sound _ 456960 128 Restriction0892_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 457088 128 Restriction0892_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
