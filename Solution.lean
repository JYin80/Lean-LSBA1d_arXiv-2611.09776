module

public import LSBA

public section

/-!
# Proofs of the statements of `Challenge.lean`

Each theorem below has the same name and the same statement as its counterpart in
`Challenge.lean`, and is proved by the theorem of the library `LSBA` named in its proof. The
definitions that occur in the statements are those of `LSBA/MainDefs.lean`.
-/

section

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix
noncomputable section
open scoped Classical
namespace LSBA

/-- (U2) Theorem 1.4 [thm:main], (1.17) [eq:main]; `x / 0 = 0` is real division. -/
theorem thm1_4 (κ : ℝ) (hκ : 0 < κ ∧ κ < 1 / 2) :
    ∃ L₀ : ℕ, ∀ L₁ : ℕ, L₀ ≤ L₁ → ∀ D τ : ℝ, 0 < D → 0 < τ →
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → ∀ g : ℝ, 0 ≤ g →
        1 - (W : ℝ) ^ (-D) ≤
          ∫ ω, (goodCountTwoSided W L (Hmat g W L ω) (bulkSet g κ L₁ L)
                  ((W : ℝ) ^ (-τ) * ellStar W L g) ((W : ℝ) ^ τ * ellStar W L g) : ℝ) /
                (countIn (Hmat g W L ω) (bulkSet g κ L₁ L) : ℝ) ∂(μ W L) :=
  main_ratio_endpoint κ hκ

end LSBA
end

end

section

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal Kronecker Matrix
noncomputable section
open scoped Classical
namespace LSBA

/-- (U3) Corollary 1.5 [cor:simultaneous], (1.18) [eq:simultaneous], every fixed threshold
`L₀`. -/
theorem cor1_5 (BL D τ κ : ℝ) (hBL : 0 < BL) (hD : 0 < D) (hτ : 0 < τ)
    (hκ : 0 < κ ∧ κ < 1 / 2) (L₀ : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ L : ℕ, 3 ≤ L → (L : ℝ) ≤ (W : ℝ) ^ BL → ∀ g : ℝ, 0 ≤ g →
      μ W L {ω | 0 < badCount W L (Hmat g W L ω) (bulkSet g κ L₀ L)
          ((W : ℝ) ^ (-τ) * ellStar W L g) +
        badCountUp W L (Hmat g W L ω) (bulkSet g κ L₀ L) ((W : ℝ) ^ τ * ellStar W L g)} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-D)) :=
  simultaneous_endpoint BL D τ κ hBL hD hτ hκ L₀

end LSBA
end

end
