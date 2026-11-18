module
public import ResultantSuperpolynomial

@[expose] public section

open Filter
open scoped Topology

namespace EPlusPiApproximation

/-- Evaluate a rational-coefficient polynomial at a real number. -/
def evalReal (x : ℝ) (p : Polynomial ℚ) : ℝ :=
  p.eval₂ (algebraMap ℚ ℝ) x

/--
Two polynomials that are Bézout-coprime cannot vanish simultaneously at
the same real number.  The hypothesis IsCoprime is an explicit identity
A * p + B * q = 1 in the rational polynomial ring.
-/
theorem coprime_polynomials_not_both_zero_at_real
    {p q : Polynomial ℚ} (hcop : IsCoprime p q) (x : ℝ) :
    evalReal x p ≠ 0 ∨ evalReal x q ≠ 0 := by
  rcases hcop with ⟨a, b, hab⟩
  have hEval := congrArg (fun r : Polynomial ℚ =>
    r.eval₂ (algebraMap ℚ ℝ) x) hab
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul',
    Polynomial.eval₂_one] at hEval
  by_cases hp : evalReal x p = 0
  · right
    intro hq
    simp [evalReal, hp, hq] at hEval
  · exact Or.inl hp

/--
A family that is pairwise Bézout-coprime has at most one member vanishing
at any fixed real number.  This is the exact role played by nonzero
resultants: two distinct members cannot share a root.
-/
theorem pairwise_coprime_family_has_at_most_one_zero
    {ι : Type*} (R : ι → Polynomial ℚ) (x : ℝ)
    (hcop : ∀ i j, i ≠ j → IsCoprime (R i) (R j)) :
    ∀ i j, evalReal x (R i) = 0 → evalReal x (R j) = 0 → i = j := by
  intro i j hi hj
  by_contra hne
  rcases coprime_polynomials_not_both_zero_at_real (hcop i j hne) x with h | h
  · exact h hi
  · exact h hj

private lemma abs_min_abs (a b : ℝ) :
    |min |a| |b|| = min |a| |b| := by
  apply abs_of_nonneg
  exact le_min (abs_nonneg a) (abs_nonneg b)

/--
Paired super-polynomial approximation contradicts a uniform fixed-power
Liouville lower bound, provided both evaluation channels are eventually
nonzero.

The upper estimate concerns only the smaller of the two values.  This is
deliberately weaker than requiring both values to be small: simultaneous
smallness of a Bézout-coprime pair is already ruled out by the resultant
identity for every real input and is therefore not, by itself, a useful
transcendence criterion.

The lower-bound hypotheses are the arithmetic input to be derived from
the resultant/minimal-polynomial height estimate.  This theorem formalizes
the final contradiction without hiding that estimate as an axiom.
-/
theorem paired_superpolynomial_smallness_conflicts_with_fixed_power_lower_bound
    {x : ℝ} {P Q : ℕ → Polynomial ℚ} {H : ℕ → ℕ} (d : ℕ)
    (hH : ∀ᶠ n : ℕ in atTop, 1 < H n)
    (hNonzeroP : ∀ᶠ n : ℕ in atTop, evalReal x (P n) ≠ 0)
    (hNonzeroQ : ∀ᶠ n : ℕ in atTop, evalReal x (Q n) ≠ 0)
    (hLowerP : ∀ᶠ n : ℕ in atTop,
      evalReal x (P n) ≠ 0 →
        1 / (H n : ℝ) ^ d ≤ |evalReal x (P n)|)
    (hLowerQ : ∀ᶠ n : ℕ in atTop,
      evalReal x (Q n) ≠ 0 →
        1 / (H n : ℝ) ^ d ≤ |evalReal x (Q n)|)
    (hSmall : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      min |evalReal x (P n)| |evalReal x (Q n)| <
        1 / (H n : ℝ) ^ k) :
    False := by
  let u : ℕ → ℝ := fun n =>
    min |evalReal x (P n)| |evalReal x (Q n)|
  have hLowerP' : ∀ᶠ n : ℕ in atTop,
      1 / (H n : ℝ) ^ d ≤ |evalReal x (P n)| := by
    filter_upwards [hLowerP, hNonzeroP] with n hL hNZ
    exact hL hNZ
  have hLowerQ' : ∀ᶠ n : ℕ in atTop,
      1 / (H n : ℝ) ^ d ≤ |evalReal x (Q n)| := by
    filter_upwards [hLowerQ, hNonzeroQ] with n hL hNZ
    exact hL hNZ
  have hLower : ∀ᶠ n : ℕ in atTop,
      1 / (H n : ℝ) ^ d ≤ |u n| := by
    filter_upwards [hLowerP', hLowerQ'] with n hP hQ
    calc
      1 / (H n : ℝ) ^ d ≤ min |evalReal x (P n)| |evalReal x (Q n)| :=
        le_min hP hQ
      _ = |u n| := (abs_min_abs _ _).symm
  have hSmall' : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      |u n| < 1 / (H n : ℝ) ^ k := by
    intro k
    filter_upwards [hSmall k] with n hn
    simpa [u, abs_min_abs] using hn
  exact no_superpolynomial_smallness_with_fixed_power_lower_bound
    d hH hLower hSmall'

#print axioms coprime_polynomials_not_both_zero_at_real
#print axioms pairwise_coprime_family_has_at_most_one_zero
#print axioms paired_superpolynomial_smallness_conflicts_with_fixed_power_lower_bound

end EPlusPiApproximation
