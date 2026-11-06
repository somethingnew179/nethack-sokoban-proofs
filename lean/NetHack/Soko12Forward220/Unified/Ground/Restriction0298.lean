import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0298_0_checked : (List.range' 152576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0298_1_checked : (List.range' 152704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0298_2_checked : (List.range' 152832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0298_3_checked : (List.range' 152960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0298_range (index : Nat) (lower : 152576 ≤ index) (upper : index < 153088) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 152832 then
    if cut : index < 152704 then
      exact segment_sound _ 152576 128 Restriction0298_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 152704 128 Restriction0298_1_checked index (by omega) (by omega)
  else
    if cut : index < 152960 then
      exact segment_sound _ 152832 128 Restriction0298_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 152960 128 Restriction0298_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
