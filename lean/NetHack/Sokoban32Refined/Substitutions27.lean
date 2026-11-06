/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions26
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub3240 (p : Pattern) : d9 (change p 161 (some 160)) = d1 p := by
  change d1 (change p 161 (some 160)) = d1 p
  exact sub3239 p
theorem sub3241 (p : Pattern) : d21 (change p 161 (some 160)) = d2 p := by
  change d2 (change p 161 (some 160)) = d2 p
  exact sub3234 p
theorem sub3242 (p : Pattern) : d746 (change p 161 (some 160)) = d1556 p := by
  change (if p 159 then d21 (change p 161 (some 160)) else d9 (change p 161 (some 160))) = d1556 p
  rw [sub3241, sub3240]
  rfl
theorem sub3243 (p : Pattern) : d747 (change p 161 (some 160)) = d1556 p := by
  change (if p 159 then d2 (change p 161 (some 160)) else d9 (change p 161 (some 160))) = d1556 p
  rw [sub3234, sub3240]
  rfl
theorem sub3244 (p : Pattern) : d748 (change p 161 (some 160)) = d1556 p := by
  change (if p 158 then d747 (change p 161 (some 160)) else d746 (change p 161 (some 160))) = d1556 p
  rw [sub3243, sub3242]
  simp only [ite_self]
theorem sub3245 (p : Pattern) : d749 (change p 161 (some 160)) = d1862 p := by
  change (if p 139 then d748 (change p 161 (some 160)) else d745 (change p 161 (some 160))) = d1862 p
  rw [sub3244, sub3238]
  rfl
theorem sub3246 (p : Pattern) : d750 (change p 161 (some 160)) = d1863 p := by
  change (if p 138 then d749 (change p 161 (some 160)) else d745 (change p 161 (some 160))) = d1863 p
  rw [sub3245, sub3238]
  rfl
theorem sub3247 (p : Pattern) : d19 (change p 161 (some 160)) = d2 p := by
  change (if p 159 then d2 (change p 161 (some 160)) else d17 (change p 161 (some 160))) = d2 p
  rw [sub3234, sub3235]
  simp only [ite_self]
theorem sub3248 (p : Pattern) : d751 (change p 161 (some 160)) = d1864 p := by
  change (if p 158 then d19 (change p 161 (some 160)) else d743 (change p 161 (some 160))) = d1864 p
  rw [sub3247, sub3236]
  rfl
theorem sub3249 (p : Pattern) : d23 (change p 161 (some 160)) = d2 p := by
  change (if p 159 then d2 (change p 161 (some 160)) else d21 (change p 161 (some 160))) = d2 p
  rw [sub3234, sub3241]
  simp only [ite_self]
theorem sub3250 (p : Pattern) : d752 (change p 161 (some 160)) = d1865 p := by
  change (if p 158 then d23 (change p 161 (some 160)) else d746 (change p 161 (some 160))) = d1865 p
  rw [sub3249, sub3242]
  rfl
theorem sub3251 (p : Pattern) : d753 (change p 161 (some 160)) = d1866 p := by
  change (if p 139 then d752 (change p 161 (some 160)) else d751 (change p 161 (some 160))) = d1866 p
  rw [sub3250, sub3248]
  rfl
theorem sub3252 (p : Pattern) : d754 (change p 161 (some 160)) = d1867 p := by
  change (if p 138 then d753 (change p 161 (some 160)) else d751 (change p 161 (some 160))) = d1867 p
  rw [sub3251, sub3248]
  rfl
theorem sub3253 (p : Pattern) : d755 (change p 161 (some 160)) = d1868 p := by
  change (if p 134 then d754 (change p 161 (some 160)) else d750 (change p 161 (some 160))) = d1868 p
  rw [sub3252, sub3246]
  rfl
theorem sub3254 (p : Pattern) : d756 (change p 161 (some 160)) = d1869 p := by
  change (if p 133 then d755 (change p 161 (some 160)) else d750 (change p 161 (some 160))) = d1869 p
  rw [sub3253, sub3246]
  rfl
theorem sub3255 (p : Pattern) : d757 (change p 161 (some 160)) = d1870 p := by
  change (if p 133 then d754 (change p 161 (some 160)) else d755 (change p 161 (some 160))) = d1870 p
  rw [sub3252, sub3253]
  rfl
theorem sub3256 (p : Pattern) : d758 (change p 161 (some 160)) = d1871 p := by
  change (if p 132 then d757 (change p 161 (some 160)) else d756 (change p 161 (some 160))) = d1871 p
  rw [sub3255, sub3254]
  rfl
theorem sub3257 (p : Pattern) : d759 (change p 161 (some 160)) = d1872 p := by
  change (if p 134 then d753 (change p 161 (some 160)) else d749 (change p 161 (some 160))) = d1872 p
  rw [sub3251, sub3245]
  rfl
theorem sub3258 (p : Pattern) : d760 (change p 161 (some 160)) = d1873 p := by
  change (if p 133 then d759 (change p 161 (some 160)) else d749 (change p 161 (some 160))) = d1873 p
  rw [sub3257, sub3245]
  rfl
theorem sub3259 (p : Pattern) : d761 (change p 161 (some 160)) = d1874 p := by
  change (if p 133 then d753 (change p 161 (some 160)) else d759 (change p 161 (some 160))) = d1874 p
  rw [sub3251, sub3257]
  rfl
theorem sub3260 (p : Pattern) : d762 (change p 161 (some 160)) = d1875 p := by
  change (if p 132 then d761 (change p 161 (some 160)) else d760 (change p 161 (some 160))) = d1875 p
  rw [sub3259, sub3258]
  rfl
theorem sub3261 (p : Pattern) : d763 (change p 161 (some 160)) = d1876 p := by
  change (if p 139 then d2 (change p 161 (some 160)) else d745 (change p 161 (some 160))) = d1876 p
  rw [sub3234, sub3238]
  rfl
theorem sub3262 (p : Pattern) : d764 (change p 161 (some 160)) = d1877 p := by
  change (if p 138 then d763 (change p 161 (some 160)) else d749 (change p 161 (some 160))) = d1877 p
  rw [sub3261, sub3245]
  rfl
theorem sub3263 (p : Pattern) : d765 (change p 161 (some 160)) = d1878 p := by
  change (if p 139 then d2 (change p 161 (some 160)) else d751 (change p 161 (some 160))) = d1878 p
  rw [sub3234, sub3248]
  rfl
theorem sub3264 (p : Pattern) : d766 (change p 161 (some 160)) = d1879 p := by
  change (if p 138 then d765 (change p 161 (some 160)) else d753 (change p 161 (some 160))) = d1879 p
  rw [sub3263, sub3251]
  rfl
theorem sub3265 (p : Pattern) : d767 (change p 161 (some 160)) = d1880 p := by
  change (if p 134 then d766 (change p 161 (some 160)) else d764 (change p 161 (some 160))) = d1880 p
  rw [sub3264, sub3262]
  rfl
theorem sub3266 (p : Pattern) : d768 (change p 161 (some 160)) = d1881 p := by
  change (if p 133 then d767 (change p 161 (some 160)) else d764 (change p 161 (some 160))) = d1881 p
  rw [sub3265, sub3262]
  rfl
theorem sub3267 (p : Pattern) : d769 (change p 161 (some 160)) = d1882 p := by
  change (if p 133 then d766 (change p 161 (some 160)) else d767 (change p 161 (some 160))) = d1882 p
  rw [sub3264, sub3265]
  rfl
theorem sub3268 (p : Pattern) : d770 (change p 161 (some 160)) = d1883 p := by
  change (if p 132 then d769 (change p 161 (some 160)) else d768 (change p 161 (some 160))) = d1883 p
  rw [sub3267, sub3266]
  rfl
theorem sub3269 (p : Pattern) : d771 (change p 161 (some 160)) = d1884 p := by
  change (if p 113 then d770 (change p 161 (some 160)) else d762 (change p 161 (some 160))) = d1884 p
  rw [sub3268, sub3260]
  rfl
theorem sub3270 (p : Pattern) : d772 (change p 161 (some 160)) = d1885 p := by
  change (if p 112 then d771 (change p 161 (some 160)) else d758 (change p 161 (some 160))) = d1885 p
  rw [sub3269, sub3256]
  rfl
theorem sub3271 (p : Pattern) : d773 (change p 161 (some 160)) = d1886 p := by
  change (if p 139 then d2 (change p 161 (some 160)) else d752 (change p 161 (some 160))) = d1886 p
  rw [sub3234, sub3250]
  rfl
theorem sub3272 (p : Pattern) : d774 (change p 161 (some 160)) = d1887 p := by
  change (if p 138 then d773 (change p 161 (some 160)) else d752 (change p 161 (some 160))) = d1887 p
  rw [sub3271, sub3250]
  rfl
theorem sub3273 (p : Pattern) : d775 (change p 161 (some 160)) = d1888 p := by
  change (if p 133 then d774 (change p 161 (some 160)) else d755 (change p 161 (some 160))) = d1888 p
  rw [sub3272, sub3253]
  rfl
theorem sub3274 (p : Pattern) : d776 (change p 161 (some 160)) = d1889 p := by
  change (if p 132 then d775 (change p 161 (some 160)) else d756 (change p 161 (some 160))) = d1889 p
  rw [sub3273, sub3254]
  rfl
theorem sub3275 (p : Pattern) : d777 (change p 161 (some 160)) = d1890 p := by
  change (if p 133 then d773 (change p 161 (some 160)) else d755 (change p 161 (some 160))) = d1890 p
  rw [sub3271, sub3253]
  rfl
theorem sub3276 (p : Pattern) : d778 (change p 161 (some 160)) = d1891 p := by
  change (if p 132 then d777 (change p 161 (some 160)) else d756 (change p 161 (some 160))) = d1891 p
  rw [sub3275, sub3254]
  rfl
theorem sub3277 (p : Pattern) : d779 (change p 161 (some 160)) = d1892 p := by
  change (if p 113 then d778 (change p 161 (some 160)) else d776 (change p 161 (some 160))) = d1892 p
  rw [sub3276, sub3274]
  rfl
theorem sub3278 (p : Pattern) : d780 (change p 161 (some 160)) = d1893 p := by
  change (if p 133 then d773 (change p 161 (some 160)) else d759 (change p 161 (some 160))) = d1893 p
  rw [sub3271, sub3257]
  rfl
theorem sub3279 (p : Pattern) : d781 (change p 161 (some 160)) = d1894 p := by
  change (if p 132 then d780 (change p 161 (some 160)) else d760 (change p 161 (some 160))) = d1894 p
  rw [sub3278, sub3258]
  rfl
theorem sub3280 (p : Pattern) : d782 (change p 161 (some 160)) = d1895 p := by
  change (if p 133 then d773 (change p 161 (some 160)) else d767 (change p 161 (some 160))) = d1895 p
  rw [sub3271, sub3265]
  rfl
theorem sub3281 (p : Pattern) : d783 (change p 161 (some 160)) = d1896 p := by
  change (if p 132 then d782 (change p 161 (some 160)) else d768 (change p 161 (some 160))) = d1896 p
  rw [sub3280, sub3266]
  rfl
theorem sub3282 (p : Pattern) : d784 (change p 161 (some 160)) = d1897 p := by
  change (if p 113 then d783 (change p 161 (some 160)) else d781 (change p 161 (some 160))) = d1897 p
  rw [sub3281, sub3279]
  rfl
theorem sub3283 (p : Pattern) : d785 (change p 161 (some 160)) = d1898 p := by
  change (if p 112 then d784 (change p 161 (some 160)) else d779 (change p 161 (some 160))) = d1898 p
  rw [sub3282, sub3277]
  rfl
theorem sub3284 (p : Pattern) : d786 (change p 161 (some 160)) = d1899 p := by
  change (if p 106 then d785 (change p 161 (some 160)) else d772 (change p 161 (some 160))) = d1899 p
  rw [sub3283, sub3270]
  rfl
theorem sub3285 (p : Pattern) : d787 (change p 161 (some 160)) = d1900 p := by
  change (if p 138 then d763 (change p 161 (some 160)) else d745 (change p 161 (some 160))) = d1900 p
  rw [sub3261, sub3238]
  rfl
theorem sub3286 (p : Pattern) : d788 (change p 161 (some 160)) = d1901 p := by
  change (if p 138 then d765 (change p 161 (some 160)) else d751 (change p 161 (some 160))) = d1901 p
  rw [sub3263, sub3248]
  rfl
theorem sub3287 (p : Pattern) : d789 (change p 161 (some 160)) = d1902 p := by
  change (if p 134 then d788 (change p 161 (some 160)) else d787 (change p 161 (some 160))) = d1902 p
  rw [sub3286, sub3285]
  rfl
theorem sub3288 (p : Pattern) : d790 (change p 161 (some 160)) = d1903 p := by
  change (if p 133 then d789 (change p 161 (some 160)) else d787 (change p 161 (some 160))) = d1903 p
  rw [sub3287, sub3285]
  rfl
theorem sub3289 (p : Pattern) : d791 (change p 161 (some 160)) = d1904 p := by
  change (if p 133 then d788 (change p 161 (some 160)) else d789 (change p 161 (some 160))) = d1904 p
  rw [sub3286, sub3287]
  rfl
theorem sub3290 (p : Pattern) : d792 (change p 161 (some 160)) = d1905 p := by
  change (if p 132 then d791 (change p 161 (some 160)) else d790 (change p 161 (some 160))) = d1905 p
  rw [sub3289, sub3288]
  rfl
theorem sub3291 (p : Pattern) : d793 (change p 161 (some 160)) = d1906 p := by
  change (if p 113 then d792 (change p 161 (some 160)) else d758 (change p 161 (some 160))) = d1906 p
  rw [sub3290, sub3256]
  rfl
theorem sub3292 (p : Pattern) : d794 (change p 161 (some 160)) = d1907 p := by
  change (if p 139 then d2 (change p 161 (some 160)) else d748 (change p 161 (some 160))) = d1907 p
  rw [sub3234, sub3244]
  rfl
theorem sub3293 (p : Pattern) : d795 (change p 161 (some 160)) = d1908 p := by
  change (if p 138 then d794 (change p 161 (some 160)) else d748 (change p 161 (some 160))) = d1908 p
  rw [sub3292, sub3244]
  rfl
theorem sub3294 (p : Pattern) : d796 (change p 161 (some 160)) = d1909 p := by
  change (if p 134 then d774 (change p 161 (some 160)) else d795 (change p 161 (some 160))) = d1909 p
  rw [sub3272, sub3293]
  rfl
theorem sub3295 (p : Pattern) : d797 (change p 161 (some 160)) = d1910 p := by
  change (if p 133 then d796 (change p 161 (some 160)) else d795 (change p 161 (some 160))) = d1910 p
  rw [sub3294, sub3293]
  rfl
theorem sub3296 (p : Pattern) : d798 (change p 161 (some 160)) = d1911 p := by
  change (if p 133 then d774 (change p 161 (some 160)) else d796 (change p 161 (some 160))) = d1911 p
  rw [sub3272, sub3294]
  rfl
theorem sub3297 (p : Pattern) : d799 (change p 161 (some 160)) = d1912 p := by
  change (if p 132 then d798 (change p 161 (some 160)) else d797 (change p 161 (some 160))) = d1912 p
  rw [sub3296, sub3295]
  rfl
theorem sub3298 (p : Pattern) : d800 (change p 161 (some 160)) = d1913 p := by
  change (if p 112 then d799 (change p 161 (some 160)) else d793 (change p 161 (some 160))) = d1913 p
  rw [sub3297, sub3291]
  rfl
theorem sub3299 (p : Pattern) : d801 (change p 161 (some 160)) = d1914 p := by
  change (if p 133 then d773 (change p 161 (some 160)) else d789 (change p 161 (some 160))) = d1914 p
  rw [sub3271, sub3287]
  rfl
theorem sub3300 (p : Pattern) : d802 (change p 161 (some 160)) = d1915 p := by
  change (if p 132 then d801 (change p 161 (some 160)) else d790 (change p 161 (some 160))) = d1915 p
  rw [sub3299, sub3288]
  rfl
theorem sub3301 (p : Pattern) : d803 (change p 161 (some 160)) = d1916 p := by
  change (if p 113 then d802 (change p 161 (some 160)) else d778 (change p 161 (some 160))) = d1916 p
  rw [sub3300, sub3276]
  rfl
theorem sub3302 (p : Pattern) : d804 (change p 161 (some 160)) = d1917 p := by
  change (if p 133 then d2 (change p 161 (some 160)) else d796 (change p 161 (some 160))) = d1917 p
  rw [sub3234, sub3294]
  rfl
theorem sub3303 (p : Pattern) : d805 (change p 161 (some 160)) = d1918 p := by
  change (if p 132 then d804 (change p 161 (some 160)) else d797 (change p 161 (some 160))) = d1918 p
  rw [sub3302, sub3295]
  rfl
theorem sub3304 (p : Pattern) : d806 (change p 161 (some 160)) = d1919 p := by
  change (if p 134 then d773 (change p 161 (some 160)) else d794 (change p 161 (some 160))) = d1919 p
  rw [sub3271, sub3292]
  rfl
theorem sub3305 (p : Pattern) : d807 (change p 161 (some 160)) = d1920 p := by
  change (if p 133 then d806 (change p 161 (some 160)) else d794 (change p 161 (some 160))) = d1920 p
  rw [sub3304, sub3292]
  rfl
theorem sub3306 (p : Pattern) : d808 (change p 161 (some 160)) = d1921 p := by
  change (if p 133 then d2 (change p 161 (some 160)) else d806 (change p 161 (some 160))) = d1921 p
  rw [sub3234, sub3304]
  rfl
theorem sub3307 (p : Pattern) : d809 (change p 161 (some 160)) = d1922 p := by
  change (if p 132 then d808 (change p 161 (some 160)) else d807 (change p 161 (some 160))) = d1922 p
  rw [sub3306, sub3305]
  rfl
theorem sub3308 (p : Pattern) : d810 (change p 161 (some 160)) = d1923 p := by
  change (if p 113 then d809 (change p 161 (some 160)) else d805 (change p 161 (some 160))) = d1923 p
  rw [sub3307, sub3303]
  rfl
theorem sub3309 (p : Pattern) : d811 (change p 161 (some 160)) = d1924 p := by
  change (if p 112 then d810 (change p 161 (some 160)) else d803 (change p 161 (some 160))) = d1924 p
  rw [sub3308, sub3301]
  rfl
theorem sub3310 (p : Pattern) : d812 (change p 161 (some 160)) = d1925 p := by
  change (if p 106 then d811 (change p 161 (some 160)) else d800 (change p 161 (some 160))) = d1925 p
  rw [sub3309, sub3298]
  rfl
theorem sub3311 (p : Pattern) : d813 (change p 161 (some 160)) = d1926 p := by
  change (if p 86 then d812 (change p 161 (some 160)) else d786 (change p 161 (some 160))) = d1926 p
  rw [sub3310, sub3284]
  rfl
theorem sub3312 (p : Pattern) : d814 (change p 161 (some 160)) = d1927 p := by
  change (if p 112 then d784 (change p 161 (some 160)) else d778 (change p 161 (some 160))) = d1927 p
  rw [sub3282, sub3276]
  rfl
theorem sub3313 (p : Pattern) : d815 (change p 161 (some 160)) = d1928 p := by
  change (if p 106 then d814 (change p 161 (some 160)) else d772 (change p 161 (some 160))) = d1928 p
  rw [sub3312, sub3270]
  rfl
theorem sub3314 (p : Pattern) : d816 (change p 161 (some 160)) = d1929 p := by
  change (if p 133 then d773 (change p 161 (some 160)) else d806 (change p 161 (some 160))) = d1929 p
  rw [sub3271, sub3304]
  rfl
theorem sub3315 (p : Pattern) : d817 (change p 161 (some 160)) = d1930 p := by
  change (if p 132 then d816 (change p 161 (some 160)) else d807 (change p 161 (some 160))) = d1930 p
  rw [sub3314, sub3305]
  rfl
theorem sub3316 (p : Pattern) : d818 (change p 161 (some 160)) = d1931 p := by
  change (if p 113 then d817 (change p 161 (some 160)) else d799 (change p 161 (some 160))) = d1931 p
  rw [sub3315, sub3297]
  rfl
theorem sub3317 (p : Pattern) : d819 (change p 161 (some 160)) = d1932 p := by
  change (if p 112 then d818 (change p 161 (some 160)) else d793 (change p 161 (some 160))) = d1932 p
  rw [sub3316, sub3291]
  rfl
theorem sub3318 (p : Pattern) : d820 (change p 161 (some 160)) = d1933 p := by
  change (if p 113 then d783 (change p 161 (some 160)) else d778 (change p 161 (some 160))) = d1933 p
  rw [sub3281, sub3276]
  rfl
theorem sub3319 (p : Pattern) : d821 (change p 161 (some 160)) = d1934 p := by
  change (if p 113 then d2 (change p 161 (some 160)) else d809 (change p 161 (some 160))) = d1934 p
  rw [sub3234, sub3307]
  rfl
theorem sub3320 (p : Pattern) : d822 (change p 161 (some 160)) = d1935 p := by
  change (if p 112 then d821 (change p 161 (some 160)) else d820 (change p 161 (some 160))) = d1935 p
  rw [sub3319, sub3318]
  rfl
theorem sub3321 (p : Pattern) : d823 (change p 161 (some 160)) = d1936 p := by
  change (if p 106 then d822 (change p 161 (some 160)) else d819 (change p 161 (some 160))) = d1936 p
  rw [sub3320, sub3317]
  rfl
theorem sub3322 (p : Pattern) : d824 (change p 161 (some 160)) = d1937 p := by
  change (if p 86 then d823 (change p 161 (some 160)) else d815 (change p 161 (some 160))) = d1937 p
  rw [sub3321, sub3313]
  rfl
theorem sub3323 (p : Pattern) : d825 (change p 161 (some 160)) = d1938 p := by
  change (if p 80 then d824 (change p 161 (some 160)) else d813 (change p 161 (some 160))) = d1938 p
  rw [sub3322, sub3311]
  rfl
theorem sub3324 (p : Pattern) : d0 (change p 139 (some 113)) = d0 p := by
  rfl
theorem sub3325 (p : Pattern) : d2 (change p 139 (some 113)) = d2 p := by
  rfl
theorem sub3326 (p : Pattern) : d3 (change p 139 (some 113)) = d3 p := by
  change (if p 161 then d2 (change p 139 (some 113)) else d0 (change p 139 (some 113))) = d3 p
  rw [sub3325, sub3324]
  rfl
theorem sub3327 (p : Pattern) : d4 (change p 139 (some 113)) = d4 p := by
  change (if p 160 then d3 (change p 139 (some 113)) else d0 (change p 139 (some 113))) = d4 p
  rw [sub3326, sub3324]
  rfl
theorem sub3328 (p : Pattern) : d5 (change p 139 (some 113)) = d5 p := by
  change (if p 160 then d2 (change p 139 (some 113)) else d0 (change p 139 (some 113))) = d5 p
  rw [sub3325, sub3324]
  rfl
theorem sub3329 (p : Pattern) : d6 (change p 139 (some 113)) = d6 p := by
  change (if p 159 then d5 (change p 139 (some 113)) else d4 (change p 139 (some 113))) = d6 p
  rw [sub3328, sub3327]
  rfl
theorem sub3330 (p : Pattern) : d7 (change p 139 (some 113)) = d7 p := by
  change (if p 159 then d2 (change p 139 (some 113)) else d4 (change p 139 (some 113))) = d7 p
  rw [sub3325, sub3327]
  rfl
theorem sub3331 (p : Pattern) : d8 (change p 139 (some 113)) = d8 p := by
  change (if p 158 then d7 (change p 139 (some 113)) else d6 (change p 139 (some 113))) = d8 p
  rw [sub3330, sub3329]
  rfl
theorem sub3332 (p : Pattern) : d456 (change p 139 (some 113)) = d8 p := by
  change d8 (change p 139 (some 113)) = d8 p
  exact sub3331 p
theorem sub3333 (p : Pattern) : d52 (change p 139 (some 113)) = d8 p := by
  change d8 (change p 139 (some 113)) = d8 p
  exact sub3331 p
theorem sub3334 (p : Pattern) : d457 (change p 139 (some 113)) = d8 p := by
  change (if p 138 then d52 (change p 139 (some 113)) else d456 (change p 139 (some 113))) = d8 p
  rw [sub3333, sub3332]
  simp only [ite_self]
theorem sub3335 (p : Pattern) : d458 (change p 139 (some 113)) = d8 p := by
  change (if p 134 then d52 (change p 139 (some 113)) else d457 (change p 139 (some 113))) = d8 p
  rw [sub3333, sub3334]
  simp only [ite_self]
theorem sub3336 (p : Pattern) : d459 (change p 139 (some 113)) = d8 p := by
  change d8 (change p 139 (some 113)) = d8 p
  exact sub3331 p
theorem sub3337 (p : Pattern) : d460 (change p 139 (some 113)) = d8 p := by
  change (if p 138 then d52 (change p 139 (some 113)) else d459 (change p 139 (some 113))) = d8 p
  rw [sub3333, sub3336]
  simp only [ite_self]
theorem sub3338 (p : Pattern) : d17 (change p 139 (some 113)) = d17 p := by
  change (if p 160 then d2 (change p 139 (some 113)) else d3 (change p 139 (some 113))) = d17 p
  rw [sub3325, sub3326]
  rfl
theorem sub3339 (p : Pattern) : d18 (change p 139 (some 113)) = d18 p := by
  change (if p 159 then d17 (change p 139 (some 113)) else d4 (change p 139 (some 113))) = d18 p
  rw [sub3338, sub3327]
  rfl
theorem sub3340 (p : Pattern) : d19 (change p 139 (some 113)) = d19 p := by
  change (if p 159 then d2 (change p 139 (some 113)) else d17 (change p 139 (some 113))) = d19 p
  rw [sub3325, sub3338]
  rfl
theorem sub3341 (p : Pattern) : d20 (change p 139 (some 113)) = d20 p := by
  change (if p 158 then d19 (change p 139 (some 113)) else d18 (change p 139 (some 113))) = d20 p
  rw [sub3340, sub3339]
  rfl
theorem sub3342 (p : Pattern) : d54 (change p 139 (some 113)) = d20 p := by
  change d20 (change p 139 (some 113)) = d20 p
  exact sub3341 p
theorem sub3343 (p : Pattern) : d461 (change p 139 (some 113)) = d1097 p := by
  change (if p 134 then d54 (change p 139 (some 113)) else d460 (change p 139 (some 113))) = d1097 p
  rw [sub3342, sub3337]
  rfl
theorem sub3344 (p : Pattern) : d462 (change p 139 (some 113)) = d1098 p := by
  change (if p 133 then d461 (change p 139 (some 113)) else d458 (change p 139 (some 113))) = d1098 p
  rw [sub3343, sub3335]
  rfl
theorem sub3345 (p : Pattern) : d1 (change p 139 (some 113)) = d1 p := by
  rfl
theorem sub3346 (p : Pattern) : d29 (change p 139 (some 113)) = d29 p := by
  change (if p 161 then d1 (change p 139 (some 113)) else d0 (change p 139 (some 113))) = d29 p
  rw [sub3345, sub3324]
  rfl
theorem sub3347 (p : Pattern) : d30 (change p 139 (some 113)) = d30 p := by
  change (if p 160 then d2 (change p 139 (some 113)) else d29 (change p 139 (some 113))) = d30 p
  rw [sub3325, sub3346]
  rfl
theorem sub3348 (p : Pattern) : d31 (change p 139 (some 113)) = d31 p := by
  change (if p 159 then d30 (change p 139 (some 113)) else d4 (change p 139 (some 113))) = d31 p
  rw [sub3347, sub3327]
  rfl
theorem sub3349 (p : Pattern) : d32 (change p 139 (some 113)) = d32 p := by
  change (if p 159 then d2 (change p 139 (some 113)) else d30 (change p 139 (some 113))) = d32 p
  rw [sub3325, sub3347]
  rfl
theorem sub3350 (p : Pattern) : d33 (change p 139 (some 113)) = d33 p := by
  change (if p 158 then d32 (change p 139 (some 113)) else d31 (change p 139 (some 113))) = d33 p
  rw [sub3349, sub3348]
  rfl
theorem sub3351 (p : Pattern) : d58 (change p 139 (some 113)) = d33 p := by
  change d33 (change p 139 (some 113)) = d33 p
  exact sub3350 p
theorem sub3352 (p : Pattern) : d463 (change p 139 (some 113)) = d1099 p := by
  change (if p 134 then d58 (change p 139 (some 113)) else d457 (change p 139 (some 113))) = d1099 p
  rw [sub3351, sub3334]
  rfl
theorem sub3353 (p : Pattern) : d37 (change p 139 (some 113)) = d37 p := by
  change (if p 159 then d2 (change p 139 (some 113)) else d5 (change p 139 (some 113))) = d37 p
  rw [sub3325, sub3328]
  rfl
theorem sub3354 (p : Pattern) : d38 (change p 139 (some 113)) = d38 p := by
  change (if p 158 then d37 (change p 139 (some 113)) else d6 (change p 139 (some 113))) = d38 p
  rw [sub3353, sub3329]
  rfl
theorem sub3355 (p : Pattern) : d464 (change p 139 (some 113)) = d38 p := by
  change d38 (change p 139 (some 113)) = d38 p
  exact sub3354 p
theorem sub3356 (p : Pattern) : d61 (change p 139 (some 113)) = d38 p := by
  change d38 (change p 139 (some 113)) = d38 p
  exact sub3354 p
theorem sub3357 (p : Pattern) : d465 (change p 139 (some 113)) = d38 p := by
  change (if p 138 then d61 (change p 139 (some 113)) else d464 (change p 139 (some 113))) = d38 p
  rw [sub3356, sub3355]
  simp only [ite_self]
theorem sub3358 (p : Pattern) : d466 (change p 139 (some 113)) = d1100 p := by
  change (if p 134 then d54 (change p 139 (some 113)) else d465 (change p 139 (some 113))) = d1100 p
  rw [sub3342, sub3357]
  rfl
theorem sub3359 (p : Pattern) : d467 (change p 139 (some 113)) = d1101 p := by
  change (if p 133 then d466 (change p 139 (some 113)) else d463 (change p 139 (some 113))) = d1101 p
  rw [sub3358, sub3352]
  rfl
end NetHack.Sokoban32Refined
