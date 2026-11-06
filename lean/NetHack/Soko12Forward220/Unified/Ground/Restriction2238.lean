import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2238_0_checked : (List.range' 1145856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2238_1_checked : (List.range' 1145984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2238_2_checked : (List.range' 1146112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2238_3_checked : (List.range' 1146240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2238_range (index : Nat) (lower : 1145856 ≤ index) (upper : index < 1146368) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1146112 then
    if cut : index < 1145984 then
      exact segment_sound _ 1145856 128 Restriction2238_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1145984 128 Restriction2238_1_checked index (by omega) (by omega)
  else
    if cut : index < 1146240 then
      exact segment_sound _ 1146112 128 Restriction2238_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1146240 128 Restriction2238_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
