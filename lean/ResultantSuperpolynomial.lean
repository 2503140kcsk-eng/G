module
public import ApproximationCriteria

@[expose] public section

open Filter
open scoped Topology

namespace EPlusPiApproximation

/--
A fixed-power lower bound is incompatible with super-polynomial decay.

This is the elementary growth obstruction used at the final stage of a
resultant-based transcendence criterion.  In the intended application,
a nonzero integer resultant gives a lower bound of the form
  H(n)^(-d) ≤ |u(n)|
for some fixed d, while the proposed approximation estimate gives
  |u(n)| < H(n)^(-k)
for every fixed k.  Taking k = d + 1 is contradictory.

The lemma deliberately isolates this last step from the harder arithmetic
work: a complete polynomial criterion must still derive the fixed-power
lower bound from nonvanishing resultants and bounds on the other conjugates.
-/
theorem no_superpolynomial_smallness_with_fixed_power_lower_bound
    {H : ℕ → ℕ} {u : ℕ → ℝ} (d : ℕ)
    (hH : ∀ᶠ n : ℕ in atTop, 1 < H n)
    (hLower : ∀ᶠ n : ℕ in atTop,
      1 / (H n : ℝ) ^ d ≤ |u n|)
    (hSmall : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      |u n| < 1 / (H n : ℝ) ^ k) :
    False := by
  have hSmall' := hSmall (d + 1)
  obtain ⟨n, hnH, hnLower, hnSmall⟩ :=
    (hH.and (hLower.and hSmall')).exists
  have hHpos : (0 : ℝ) < (H n : ℝ) := by
    exact_mod_cast (show 0 < H n by omega)
  have hHgt : (1 : ℝ) < (H n : ℝ) := by
    exact_mod_cast hnH
  have hpow : (H n : ℝ) ^ d < (H n : ℝ) ^ (d + 1) := by
    rw [pow_succ]
    calc
      (H n : ℝ) ^ d = (H n : ℝ) ^ d * 1 := by ring
      _ < (H n : ℝ) ^ d * (H n : ℝ) :=
        mul_lt_mul_of_pos_left hHgt (pow_pos hHpos d)
      _ = (H n : ℝ) ^ (d + 1) := by rw [pow_succ]
  have hinv :
      1 / (H n : ℝ) ^ (d + 1) < 1 / (H n : ℝ) ^ d := by
    apply (div_lt_div_iff₀ (pow_pos hHpos (d + 1)) (pow_pos hHpos d)).2
    simpa using hpow
  have hcontra :
      1 / (H n : ℝ) ^ d < 1 / (H n : ℝ) ^ d :=
    lt_of_le_of_lt hnLower (lt_trans hnSmall hinv)
  exact (lt_irrefl _ hcontra)

#print axioms no_superpolynomial_smallness_with_fixed_power_lower_bound

end EPlusPiApproximation
