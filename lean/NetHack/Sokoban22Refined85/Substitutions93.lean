/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions92
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub11160 (p : Pattern) : d2660 (change p 225 (some 224)) = d6074 p := by
  change (if p 160 then d2563 (change p 225 (some 224)) else d2659 (change p 225 (some 224))) = d6074 p
  rw [sub11054, sub11159]
  rfl
theorem sub11161 (p : Pattern) : d2661 (change p 225 (some 224)) = d6078 p := by
  change (if p 163 then d2573 (change p 225 (some 224)) else d2516 (change p 225 (some 224))) = d6078 p
  rw [sub11067, sub10984]
  rfl
theorem sub11162 (p : Pattern) : d2662 (change p 225 (some 224)) = d6080 p := by
  change (if p 162 then d2575 (change p 225 (some 224)) else d2661 (change p 225 (some 224))) = d6080 p
  rw [sub11069, sub11161]
  rfl
theorem sub11163 (p : Pattern) : d2663 (change p 225 (some 224)) = d6089 p := by
  change (if p 161 then d2586 (change p 225 (some 224)) else d2662 (change p 225 (some 224))) = d6089 p
  rw [sub11085, sub11162]
  rfl
theorem sub11164 (p : Pattern) : d2664 (change p 225 (some 224)) = d6100 p := by
  change (if p 160 then d2597 (change p 225 (some 224)) else d2663 (change p 225 (some 224))) = d6100 p
  rw [sub11096, sub11163]
  rfl
theorem sub11165 (p : Pattern) : d2665 (change p 225 (some 224)) = d6101 p := by
  change (if p 141 then d2664 (change p 225 (some 224)) else d2660 (change p 225 (some 224))) = d6101 p
  rw [sub11164, sub11160]
  rfl
theorem sub11166 (p : Pattern) : d2666 (change p 225 (some 224)) = d6131 p := by
  change (if p 138 then d2628 (change p 225 (some 224)) else d2665 (change p 225 (some 224))) = d6131 p
  rw [sub11129, sub11165]
  rfl
theorem sub11167 (p : Pattern) : d2667 (change p 225 (some 224)) = d6141 p := by
  change (if p 116 then d2638 (change p 225 (some 224)) else d2666 (change p 225 (some 224))) = d6141 p
  rw [sub11139, sub11166]
  rfl
theorem sub11168 (p : Pattern) : d2668 (change p 225 (some 224)) = d6051 p := by
  change (if p 162 then d2528 (change p 225 (some 224)) else d2519 (change p 225 (some 224))) = d6051 p
  rw [sub11005, sub10987]
  rfl
theorem sub11169 (p : Pattern) : d2669 (change p 225 (some 224)) = d6057 p := by
  change (if p 161 then d2538 (change p 225 (some 224)) else d2668 (change p 225 (some 224))) = d6057 p
  rw [sub11024, sub11168]
  rfl
theorem sub11170 (p : Pattern) : d2670 (change p 225 (some 224)) = d6074 p := by
  change (if p 160 then d2563 (change p 225 (some 224)) else d2669 (change p 225 (some 224))) = d6074 p
  rw [sub11054, sub11169]
  rfl
theorem sub11171 (p : Pattern) : d2671 (change p 225 (some 224)) = d6101 p := by
  change (if p 141 then d2647 (change p 225 (some 224)) else d2670 (change p 225 (some 224))) = d6101 p
  rw [sub11148, sub11170]
  rfl
theorem sub11172 (p : Pattern) : d2672 (change p 225 (some 224)) = d6131 p := by
  change (if p 138 then d2628 (change p 225 (some 224)) else d2671 (change p 225 (some 224))) = d6131 p
  rw [sub11129, sub11171]
  rfl
theorem sub11173 (p : Pattern) : d2673 (change p 225 (some 224)) = d6143 p := by
  change (if p 116 then d2650 (change p 225 (some 224)) else d2672 (change p 225 (some 224))) = d6143 p
  rw [sub11151, sub11172]
  rfl
theorem sub11174 (p : Pattern) : d2674 (change p 225 (some 224)) = d6144 p := by
  change (if p 115 then d2673 (change p 225 (some 224)) else d2667 (change p 225 (some 224))) = d6144 p
  rw [sub11173, sub11167]
  rfl
theorem sub11175 (p : Pattern) : d2675 (change p 225 (some 224)) = d6144 p := by
  change (if p 71 then d2674 (change p 225 (some 224)) else d2652 (change p 225 (some 224))) = d6144 p
  rw [sub11174, sub11153]
  simp only [ite_self]
theorem sub11176 (p : Pattern) : d1 (change p 225 (some 224)) = d1 p := by
  rfl
theorem sub11177 (p : Pattern) : d102 (change p 225 (some 224)) = d102 p := by
  change (if p 247 then d12 (change p 225 (some 224)) else d1 (change p 225 (some 224))) = d102 p
  rw [sub10962, sub11176]
  rfl
theorem sub11178 (p : Pattern) : d103 (change p 225 (some 224)) = d103 p := by
  change (if p 246 then d102 (change p 225 (some 224)) else d1 (change p 225 (some 224))) = d103 p
  rw [sub11177, sub11176]
  rfl
theorem sub11179 (p : Pattern) : d2677 (change p 225 (some 224)) = d103 p := by
  change d103 (change p 225 (some 224)) = d103 p
  exact sub11178 p
theorem sub11180 (p : Pattern) : d2678 (change p 225 (some 224)) = d103 p := by
  change d2677 (change p 225 (some 224)) = d103 p
  exact sub11179 p
theorem sub11181 (p : Pattern) : d5 (change p 225 (some 224)) = d5 p := by
  rfl
theorem sub11182 (p : Pattern) : d1939 (change p 225 (some 224)) = d1939 p := by
  change (if p 247 then d5 (change p 225 (some 224)) else d1 (change p 225 (some 224))) = d1939 p
  rw [sub11181, sub11176]
  rfl
theorem sub11183 (p : Pattern) : d106 (change p 225 (some 224)) = d106 p := by
  change (if p 247 then d12 (change p 225 (some 224)) else d5 (change p 225 (some 224))) = d106 p
  rw [sub10962, sub11181]
  rfl
theorem sub11184 (p : Pattern) : d1940 (change p 225 (some 224)) = d1940 p := by
  change (if p 246 then d106 (change p 225 (some 224)) else d1939 (change p 225 (some 224))) = d1940 p
  rw [sub11183, sub11182]
  rfl
theorem sub11185 (p : Pattern) : d2679 (change p 225 (some 224)) = d1940 p := by
  change d1940 (change p 225 (some 224)) = d1940 p
  exact sub11184 p
theorem sub11186 (p : Pattern) : d2680 (change p 225 (some 224)) = d1940 p := by
  change d2679 (change p 225 (some 224)) = d1940 p
  exact sub11185 p
theorem sub11187 (p : Pattern) : d2681 (change p 225 (some 224)) = d6145 p := by
  change (if p 204 then d2680 (change p 225 (some 224)) else d2678 (change p 225 (some 224))) = d6145 p
  rw [sub11186, sub11180]
  rfl
theorem sub11188 (p : Pattern) : d3 (change p 225 (some 224)) = d3 p := by
  rfl
theorem sub11189 (p : Pattern) : d1872 (change p 225 (some 224)) = d1872 p := by
  change (if p 247 then d3 (change p 225 (some 224)) else d1 (change p 225 (some 224))) = d1872 p
  rw [sub11188, sub11176]
  rfl
theorem sub11190 (p : Pattern) : d115 (change p 225 (some 224)) = d115 p := by
  change (if p 247 then d12 (change p 225 (some 224)) else d3 (change p 225 (some 224))) = d115 p
  rw [sub10962, sub11188]
  rfl
theorem sub11191 (p : Pattern) : d1873 (change p 225 (some 224)) = d1873 p := by
  change (if p 246 then d115 (change p 225 (some 224)) else d1872 (change p 225 (some 224))) = d1873 p
  rw [sub11190, sub11189]
  rfl
theorem sub11192 (p : Pattern) : d2682 (change p 225 (some 224)) = d1873 p := by
  change d1873 (change p 225 (some 224)) = d1873 p
  exact sub11191 p
theorem sub11193 (p : Pattern) : d2683 (change p 225 (some 224)) = d1873 p := by
  change d2682 (change p 225 (some 224)) = d1873 p
  exact sub11192 p
theorem sub11194 (p : Pattern) : d2684 (change p 225 (some 224)) = d6146 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2683 (change p 225 (some 224))) = d6146 p
  rw [sub10962, sub11193]
  rfl
theorem sub11195 (p : Pattern) : d2685 (change p 225 (some 224)) = d6147 p := by
  change (if p 182 then d2684 (change p 225 (some 224)) else d2681 (change p 225 (some 224))) = d6147 p
  rw [sub11194, sub11187]
  rfl
theorem sub11196 (p : Pattern) : d2686 (change p 225 (some 224)) = d6145 p := by
  change (if p 204 then d2680 (change p 225 (some 224)) else d2677 (change p 225 (some 224))) = d6145 p
  rw [sub11186, sub11179]
  rfl
theorem sub11197 (p : Pattern) : d2687 (change p 225 (some 224)) = d6147 p := by
  change (if p 182 then d2684 (change p 225 (some 224)) else d2686 (change p 225 (some 224))) = d6147 p
  rw [sub11194, sub11196]
  rfl
theorem sub11198 (p : Pattern) : d2688 (change p 225 (some 224)) = d6147 p := by
  change (if p 163 then d2687 (change p 225 (some 224)) else d2685 (change p 225 (some 224))) = d6147 p
  rw [sub11197, sub11195]
  simp only [ite_self]
theorem sub11199 (p : Pattern) : d107 (change p 225 (some 224)) = d107 p := by
  change (if p 246 then d106 (change p 225 (some 224)) else d5 (change p 225 (some 224))) = d107 p
  rw [sub11183, sub11181]
  rfl
theorem sub11200 (p : Pattern) : d2689 (change p 225 (some 224)) = d107 p := by
  change d107 (change p 225 (some 224)) = d107 p
  exact sub11199 p
theorem sub11201 (p : Pattern) : d1963 (change p 225 (some 224)) = d1963 p := by
  change (if p 247 then d9 (change p 225 (some 224)) else d5 (change p 225 (some 224))) = d1963 p
  rw [sub11007, sub11181]
  rfl
theorem sub11202 (p : Pattern) : d1964 (change p 225 (some 224)) = d1964 p := by
  change (if p 246 then d23 (change p 225 (some 224)) else d1963 (change p 225 (some 224))) = d1964 p
  rw [sub11008, sub11201]
  rfl
theorem sub11203 (p : Pattern) : d2690 (change p 225 (some 224)) = d1964 p := by
  change d1964 (change p 225 (some 224)) = d1964 p
  exact sub11202 p
theorem sub11204 (p : Pattern) : d2691 (change p 225 (some 224)) = d1964 p := by
  change d2690 (change p 225 (some 224)) = d1964 p
  exact sub11203 p
theorem sub11205 (p : Pattern) : d2692 (change p 225 (some 224)) = d6148 p := by
  change (if p 204 then d2691 (change p 225 (some 224)) else d2689 (change p 225 (some 224))) = d6148 p
  rw [sub11204, sub11200]
  rfl
theorem sub11206 (p : Pattern) : d7 (change p 225 (some 224)) = d7 p := by
  rfl
theorem sub11207 (p : Pattern) : d1880 (change p 225 (some 224)) = d1880 p := by
  change (if p 247 then d7 (change p 225 (some 224)) else d5 (change p 225 (some 224))) = d1880 p
  rw [sub11206, sub11181]
  rfl
theorem sub11208 (p : Pattern) : d119 (change p 225 (some 224)) = d119 p := by
  change (if p 247 then d12 (change p 225 (some 224)) else d7 (change p 225 (some 224))) = d119 p
  rw [sub10962, sub11206]
  rfl
theorem sub11209 (p : Pattern) : d1881 (change p 225 (some 224)) = d1881 p := by
  change (if p 246 then d119 (change p 225 (some 224)) else d1880 (change p 225 (some 224))) = d1881 p
  rw [sub11208, sub11207]
  rfl
theorem sub11210 (p : Pattern) : d2693 (change p 225 (some 224)) = d1881 p := by
  change d1881 (change p 225 (some 224)) = d1881 p
  exact sub11209 p
theorem sub11211 (p : Pattern) : d2694 (change p 225 (some 224)) = d1881 p := by
  change d2693 (change p 225 (some 224)) = d1881 p
  exact sub11210 p
theorem sub11212 (p : Pattern) : d2695 (change p 225 (some 224)) = d6149 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2694 (change p 225 (some 224))) = d6149 p
  rw [sub10962, sub11211]
  rfl
theorem sub11213 (p : Pattern) : d2696 (change p 225 (some 224)) = d6150 p := by
  change (if p 182 then d2695 (change p 225 (some 224)) else d2692 (change p 225 (some 224))) = d6150 p
  rw [sub11212, sub11205]
  rfl
theorem sub11214 (p : Pattern) : d2697 (change p 225 (some 224)) = d6151 p := by
  change (if p 163 then d2696 (change p 225 (some 224)) else d2687 (change p 225 (some 224))) = d6151 p
  rw [sub11213, sub11197]
  rfl
theorem sub11215 (p : Pattern) : d2698 (change p 225 (some 224)) = d6152 p := by
  change (if p 162 then d2697 (change p 225 (some 224)) else d2688 (change p 225 (some 224))) = d6152 p
  rw [sub11214, sub11198]
  rfl
theorem sub11216 (p : Pattern) : d2699 (change p 225 (some 224)) = d6153 p := by
  change (if p 163 then d12 (change p 225 (some 224)) else d2581 (change p 225 (some 224))) = d6153 p
  rw [sub10962, sub11078]
  rfl
theorem sub11217 (p : Pattern) : d2700 (change p 225 (some 224)) = d6154 p := by
  change (if p 162 then d2699 (change p 225 (some 224)) else d2697 (change p 225 (some 224))) = d6154 p
  rw [sub11216, sub11214]
  rfl
theorem sub11218 (p : Pattern) : d2701 (change p 225 (some 224)) = d6155 p := by
  change (if p 161 then d2700 (change p 225 (some 224)) else d2698 (change p 225 (some 224))) = d6155 p
  rw [sub11217, sub11215]
  rfl
theorem sub11219 (p : Pattern) : d1894 (change p 225 (some 224)) = d1894 p := by
  change (if p 247 then d7 (change p 225 (some 224)) else d3 (change p 225 (some 224))) = d1894 p
  rw [sub11206, sub11188]
  rfl
theorem sub11220 (p : Pattern) : d1895 (change p 225 (some 224)) = d1895 p := by
  change (if p 246 then d119 (change p 225 (some 224)) else d1894 (change p 225 (some 224))) = d1895 p
  rw [sub11208, sub11219]
  rfl
theorem sub11221 (p : Pattern) : d2703 (change p 225 (some 224)) = d1895 p := by
  change d1895 (change p 225 (some 224)) = d1895 p
  exact sub11220 p
theorem sub11222 (p : Pattern) : d2704 (change p 225 (some 224)) = d1895 p := by
  change d2703 (change p 225 (some 224)) = d1895 p
  exact sub11221 p
theorem sub11223 (p : Pattern) : d2705 (change p 225 (some 224)) = d6156 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2704 (change p 225 (some 224))) = d6156 p
  rw [sub10962, sub11222]
  rfl
theorem sub11224 (p : Pattern) : d2706 (change p 225 (some 224)) = d6157 p := by
  change (if p 182 then d2705 (change p 225 (some 224)) else d2686 (change p 225 (some 224))) = d6157 p
  rw [sub11223, sub11196]
  rfl
theorem sub11225 (p : Pattern) : d1902 (change p 225 (some 224)) = d1902 p := by
  change (if p 247 then d11 (change p 225 (some 224)) else d7 (change p 225 (some 224))) = d1902 p
  rw [sub11015, sub11206]
  rfl
theorem sub11226 (p : Pattern) : d1903 (change p 225 (some 224)) = d1903 p := by
  change (if p 246 then d39 (change p 225 (some 224)) else d1902 (change p 225 (some 224))) = d1903 p
  rw [sub11017, sub11225]
  rfl
theorem sub11227 (p : Pattern) : d2708 (change p 225 (some 224)) = d1903 p := by
  change d1903 (change p 225 (some 224)) = d1903 p
  exact sub11226 p
theorem sub11228 (p : Pattern) : d2709 (change p 225 (some 224)) = d1903 p := by
  change d2708 (change p 225 (some 224)) = d1903 p
  exact sub11227 p
theorem sub11229 (p : Pattern) : d2710 (change p 225 (some 224)) = d6158 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2709 (change p 225 (some 224))) = d6158 p
  rw [sub10962, sub11228]
  rfl
theorem sub11230 (p : Pattern) : d2711 (change p 225 (some 224)) = d6159 p := by
  change (if p 182 then d2710 (change p 225 (some 224)) else d2686 (change p 225 (some 224))) = d6159 p
  rw [sub11229, sub11196]
  rfl
theorem sub11231 (p : Pattern) : d2712 (change p 225 (some 224)) = d6160 p := by
  change (if p 163 then d2711 (change p 225 (some 224)) else d2706 (change p 225 (some 224))) = d6160 p
  rw [sub11230, sub11224]
  rfl
theorem sub11232 (p : Pattern) : d2713 (change p 225 (some 224)) = d6161 p := by
  change (if p 182 then d12 (change p 225 (some 224)) else d2686 (change p 225 (some 224))) = d6161 p
  rw [sub10962, sub11196]
  rfl
theorem sub11233 (p : Pattern) : d2714 (change p 225 (some 224)) = d6162 p := by
  change (if p 182 then d12 (change p 225 (some 224)) else d2692 (change p 225 (some 224))) = d6162 p
  rw [sub10962, sub11205]
  rfl
theorem sub11234 (p : Pattern) : d2715 (change p 225 (some 224)) = d6163 p := by
  change (if p 163 then d2714 (change p 225 (some 224)) else d2713 (change p 225 (some 224))) = d6163 p
  rw [sub11233, sub11232]
  rfl
theorem sub11235 (p : Pattern) : d2716 (change p 225 (some 224)) = d6164 p := by
  change (if p 162 then d2715 (change p 225 (some 224)) else d2712 (change p 225 (some 224))) = d6164 p
  rw [sub11234, sub11231]
  rfl
theorem sub11236 (p : Pattern) : d2717 (change p 225 (some 224)) = d6165 p := by
  change (if p 163 then d12 (change p 225 (some 224)) else d2592 (change p 225 (some 224))) = d6165 p
  rw [sub10962, sub11091]
  rfl
theorem sub11237 (p : Pattern) : d2718 (change p 225 (some 224)) = d6166 p := by
  change (if p 162 then d2717 (change p 225 (some 224)) else d2715 (change p 225 (some 224))) = d6166 p
  rw [sub11236, sub11234]
  rfl
theorem sub11238 (p : Pattern) : d2719 (change p 225 (some 224)) = d6167 p := by
  change (if p 161 then d2718 (change p 225 (some 224)) else d2716 (change p 225 (some 224))) = d6167 p
  rw [sub11237, sub11235]
  rfl
theorem sub11239 (p : Pattern) : d2720 (change p 225 (some 224)) = d6168 p := by
  change (if p 160 then d2719 (change p 225 (some 224)) else d2701 (change p 225 (some 224))) = d6168 p
  rw [sub11238, sub11218]
  rfl
theorem sub11240 (p : Pattern) : d2722 (change p 225 (some 224)) = d103 p := by
  change d2677 (change p 225 (some 224)) = d103 p
  exact sub11179 p
theorem sub11241 (p : Pattern) : d2723 (change p 225 (some 224)) = d6145 p := by
  change (if p 204 then d2680 (change p 225 (some 224)) else d2722 (change p 225 (some 224))) = d6145 p
  rw [sub11186, sub11240]
  rfl
theorem sub11242 (p : Pattern) : d2724 (change p 225 (some 224)) = d6147 p := by
  change (if p 182 then d2684 (change p 225 (some 224)) else d2723 (change p 225 (some 224))) = d6147 p
  rw [sub11194, sub11241]
  rfl
theorem sub11243 (p : Pattern) : d116 (change p 225 (some 224)) = d116 p := by
  change (if p 246 then d115 (change p 225 (some 224)) else d3 (change p 225 (some 224))) = d116 p
  rw [sub11190, sub11188]
  rfl
theorem sub11244 (p : Pattern) : d2702 (change p 225 (some 224)) = d116 p := by
  change d116 (change p 225 (some 224)) = d116 p
  exact sub11243 p
theorem sub11245 (p : Pattern) : d2725 (change p 225 (some 224)) = d6169 p := by
  change (if p 204 then d2704 (change p 225 (some 224)) else d2702 (change p 225 (some 224))) = d6169 p
  rw [sub11222, sub11244]
  rfl
theorem sub11246 (p : Pattern) : d1918 (change p 225 (some 224)) = d1918 p := by
  change (if p 247 then d5 (change p 225 (some 224)) else d3 (change p 225 (some 224))) = d1918 p
  rw [sub11181, sub11188]
  rfl
theorem sub11247 (p : Pattern) : d1919 (change p 225 (some 224)) = d1919 p := by
  change (if p 246 then d106 (change p 225 (some 224)) else d1918 (change p 225 (some 224))) = d1919 p
  rw [sub11183, sub11246]
  rfl
theorem sub11248 (p : Pattern) : d2726 (change p 225 (some 224)) = d1919 p := by
  change d1919 (change p 225 (some 224)) = d1919 p
  exact sub11247 p
theorem sub11249 (p : Pattern) : d2727 (change p 225 (some 224)) = d1919 p := by
  change d2726 (change p 225 (some 224)) = d1919 p
  exact sub11248 p
theorem sub11250 (p : Pattern) : d2728 (change p 225 (some 224)) = d6170 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2727 (change p 225 (some 224))) = d6170 p
  rw [sub10962, sub11249]
  rfl
theorem sub11251 (p : Pattern) : d2729 (change p 225 (some 224)) = d6171 p := by
  change (if p 182 then d2728 (change p 225 (some 224)) else d2725 (change p 225 (some 224))) = d6171 p
  rw [sub11250, sub11245]
  rfl
theorem sub11252 (p : Pattern) : d2730 (change p 225 (some 224)) = d6172 p := by
  change (if p 163 then d2729 (change p 225 (some 224)) else d2724 (change p 225 (some 224))) = d6172 p
  rw [sub11251, sub11242]
  rfl
theorem sub11253 (p : Pattern) : d2731 (change p 225 (some 224)) = d6173 p := by
  change (if p 163 then d2581 (change p 225 (some 224)) else d2696 (change p 225 (some 224))) = d6173 p
  rw [sub11078, sub11213]
  rfl
theorem sub11254 (p : Pattern) : d2732 (change p 225 (some 224)) = d6174 p := by
  change (if p 162 then d2731 (change p 225 (some 224)) else d2730 (change p 225 (some 224))) = d6174 p
  rw [sub11253, sub11252]
  rfl
theorem sub11255 (p : Pattern) : d2733 (change p 225 (some 224)) = d6175 p := by
  change (if p 163 then d2584 (change p 225 (some 224)) else d2696 (change p 225 (some 224))) = d6175 p
  rw [sub11083, sub11213]
  rfl
theorem sub11256 (p : Pattern) : d2734 (change p 225 (some 224)) = d6176 p := by
  change (if p 162 then d12 (change p 225 (some 224)) else d2733 (change p 225 (some 224))) = d6176 p
  rw [sub10962, sub11255]
  rfl
theorem sub11257 (p : Pattern) : d2735 (change p 225 (some 224)) = d6177 p := by
  change (if p 161 then d2734 (change p 225 (some 224)) else d2732 (change p 225 (some 224))) = d6177 p
  rw [sub11256, sub11254]
  rfl
theorem sub11258 (p : Pattern) : d2736 (change p 225 (some 224)) = d6178 p := by
  change (if p 182 then d12 (change p 225 (some 224)) else d2725 (change p 225 (some 224))) = d6178 p
  rw [sub10962, sub11245]
  rfl
theorem sub11259 (p : Pattern) : d2737 (change p 225 (some 224)) = d6179 p := by
  change (if p 163 then d2736 (change p 225 (some 224)) else d2711 (change p 225 (some 224))) = d6179 p
  rw [sub11258, sub11230]
  rfl
theorem sub11260 (p : Pattern) : d2738 (change p 225 (some 224)) = d6180 p := by
  change (if p 163 then d2592 (change p 225 (some 224)) else d2714 (change p 225 (some 224))) = d6180 p
  rw [sub11091, sub11233]
  rfl
theorem sub11261 (p : Pattern) : d2739 (change p 225 (some 224)) = d6181 p := by
  change (if p 162 then d2738 (change p 225 (some 224)) else d2737 (change p 225 (some 224))) = d6181 p
  rw [sub11260, sub11259]
  rfl
theorem sub11262 (p : Pattern) : d2740 (change p 225 (some 224)) = d6182 p := by
  change (if p 163 then d2594 (change p 225 (some 224)) else d2714 (change p 225 (some 224))) = d6182 p
  rw [sub11093, sub11233]
  rfl
theorem sub11263 (p : Pattern) : d2741 (change p 225 (some 224)) = d6183 p := by
  change (if p 162 then d12 (change p 225 (some 224)) else d2740 (change p 225 (some 224))) = d6183 p
  rw [sub10962, sub11262]
  rfl
theorem sub11264 (p : Pattern) : d2742 (change p 225 (some 224)) = d6184 p := by
  change (if p 161 then d2741 (change p 225 (some 224)) else d2739 (change p 225 (some 224))) = d6184 p
  rw [sub11263, sub11261]
  rfl
theorem sub11265 (p : Pattern) : d2743 (change p 225 (some 224)) = d6185 p := by
  change (if p 160 then d2742 (change p 225 (some 224)) else d2735 (change p 225 (some 224))) = d6185 p
  rw [sub11264, sub11257]
  rfl
theorem sub11266 (p : Pattern) : d2744 (change p 225 (some 224)) = d6186 p := by
  change (if p 141 then d2743 (change p 225 (some 224)) else d2720 (change p 225 (some 224))) = d6186 p
  rw [sub11265, sub11239]
  rfl
theorem sub11267 (p : Pattern) : d2745 (change p 225 (some 224)) = d6187 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2680 (change p 225 (some 224))) = d6187 p
  rw [sub10962, sub11186]
  rfl
theorem sub11268 (p : Pattern) : d2746 (change p 225 (some 224)) = d6188 p := by
  change (if p 182 then d2745 (change p 225 (some 224)) else d2686 (change p 225 (some 224))) = d6188 p
  rw [sub11267, sub11196]
  rfl
theorem sub11269 (p : Pattern) : d2747 (change p 225 (some 224)) = d6189 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2691 (change p 225 (some 224))) = d6189 p
  rw [sub10962, sub11204]
  rfl
theorem sub11270 (p : Pattern) : d2748 (change p 225 (some 224)) = d6190 p := by
  change (if p 182 then d2747 (change p 225 (some 224)) else d2692 (change p 225 (some 224))) = d6190 p
  rw [sub11269, sub11205]
  rfl
theorem sub11271 (p : Pattern) : d2749 (change p 225 (some 224)) = d6191 p := by
  change (if p 163 then d2748 (change p 225 (some 224)) else d2746 (change p 225 (some 224))) = d6191 p
  rw [sub11270, sub11268]
  rfl
theorem sub11272 (p : Pattern) : d2750 (change p 225 (some 224)) = d6192 p := by
  change (if p 162 then d2749 (change p 225 (some 224)) else d2746 (change p 225 (some 224))) = d6192 p
  rw [sub11271, sub11268]
  rfl
theorem sub11273 (p : Pattern) : d2751 (change p 225 (some 224)) = d6193 p := by
  change (if p 162 then d2699 (change p 225 (some 224)) else d2749 (change p 225 (some 224))) = d6193 p
  rw [sub11216, sub11271]
  rfl
theorem sub11274 (p : Pattern) : d2752 (change p 225 (some 224)) = d6194 p := by
  change (if p 161 then d2751 (change p 225 (some 224)) else d2750 (change p 225 (some 224))) = d6194 p
  rw [sub11273, sub11272]
  rfl
theorem sub11275 (p : Pattern) : d2753 (change p 225 (some 224)) = d6195 p := by
  change (if p 182 then d2705 (change p 225 (some 224)) else d2725 (change p 225 (some 224))) = d6195 p
  rw [sub11223, sub11245]
  rfl
theorem sub11276 (p : Pattern) : d120 (change p 225 (some 224)) = d120 p := by
  change (if p 246 then d119 (change p 225 (some 224)) else d7 (change p 225 (some 224))) = d120 p
  rw [sub11208, sub11206]
  rfl
theorem sub11277 (p : Pattern) : d2707 (change p 225 (some 224)) = d120 p := by
  change d120 (change p 225 (some 224)) = d120 p
  exact sub11276 p
theorem sub11278 (p : Pattern) : d2754 (change p 225 (some 224)) = d6196 p := by
  change (if p 204 then d2709 (change p 225 (some 224)) else d2707 (change p 225 (some 224))) = d6196 p
  rw [sub11228, sub11277]
  rfl
theorem sub11279 (p : Pattern) : d2755 (change p 225 (some 224)) = d6197 p := by
  change (if p 182 then d2710 (change p 225 (some 224)) else d2754 (change p 225 (some 224))) = d6197 p
  rw [sub11229, sub11278]
  rfl
end NetHack.Sokoban22Refined85
