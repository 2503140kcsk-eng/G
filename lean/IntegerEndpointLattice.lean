module
public import Mathlib

@[expose] public section

/-!
# Primitive rank-one endpoint arithmetic

A Bezout identity certifies that the pair (a,b) is primitive. If another
integer pair (c,d) is collinear with it (zero 2x2 determinant), then that
pair is an integer multiple of (a,b). This is the elementary saturation
step used when identifying rank-one endpoint kernels.
-/

namespace EPlusPiApproximation

/--
If (a,b) is primitive in the Bezout sense and (c,d) is collinear with it,
then (c,d) is an integer multiple of (a,b).

The determinant hypothesis is a*d = b*c. The Bezout witness is the
integral certificate of primitivity. In lattice applications, the determinant
condition is obtained from rational rank one, while the Bezout witness comes
from gcd normalization.
-/
theorem integer_pair_multiple_of_bezout_and_determinant
    {a b c d : ℤ}
    (hbez : ∃ u v : ℤ, u * a + v * b = 1)
    (hdet : a * d = b * c) :
    ∃ k : ℤ, c = k * a ∧ d = k * b := by
  obtain ⟨u, v, hbez⟩ := hbez
  refine ⟨u * c + v * d, ?_, ?_⟩
  · have h : (u * c + v * d) * a = c := by
      calc
        (u * c + v * d) * a = u * (a * c) + v * (a * d) := by ring
        _ = u * (a * c) + v * (b * c) := by rw [hdet]
        _ = (u * a + v * b) * c := by ring
        _ = c := by rw [hbez]; ring
    exact h.symm
  · have h : (u * c + v * d) * b = d := by
      calc
        (u * c + v * d) * b = u * (b * c) + v * (b * d) := by ring
        _ = u * (a * d) + v * (b * d) := by rw [← hdet]
        _ = (u * a + v * b) * d := by ring
        _ = d := by rw [hbez]; ring
    exact h.symm

#print axioms integer_pair_multiple_of_bezout_and_determinant

end EPlusPiApproximation
