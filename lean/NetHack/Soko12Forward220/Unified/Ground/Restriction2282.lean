import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2282_0_checked : (List.range' 1168384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2282_1_checked : (List.range' 1168512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2282_2_checked : (List.range' 1168640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2282_3_checked : (List.range' 1168768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2282_range (index : Nat) (lower : 1168384 ≤ index) (upper : index < 1168896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1168640 then
    if cut : index < 1168512 then
      exact segment_sound _ 1168384 128 Restriction2282_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1168512 128 Restriction2282_1_checked index (by omega) (by omega)
  else
    if cut : index < 1168768 then
      exact segment_sound _ 1168640 128 Restriction2282_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1168768 128 Restriction2282_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
