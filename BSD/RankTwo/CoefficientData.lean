import Mathlib.Data.Fin.VecNotation

namespace BSD.RankTwo

/-- The finite coefficient table used by the level-389 Mellin estimate.
The arithmetic identification with the curve is proved separately. -/
def firstCoefficients (i : Fin 18) : ℤ :=
  ![0, 1, -2, -2, 2, -3, 4, -5, 0, 1, 6, -4, -4, -3, 10, 6, -4, -6] i

end BSD.RankTwo
