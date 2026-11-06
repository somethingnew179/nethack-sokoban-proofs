import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2235_0_checked : (List.range' 1144320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2235_1_checked : (List.range' 1144448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2235_2_checked : (List.range' 1144576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2235_3_checked : (List.range' 1144704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2235_range (index : Nat) (lower : 1144320 ≤ index) (upper : index < 1144832) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1144576 then
    if cut : index < 1144448 then
      exact segment_sound _ 1144320 128 Restriction2235_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1144448 128 Restriction2235_1_checked index (by omega) (by omega)
  else
    if cut : index < 1144704 then
      exact segment_sound _ 1144576 128 Restriction2235_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1144704 128 Restriction2235_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
