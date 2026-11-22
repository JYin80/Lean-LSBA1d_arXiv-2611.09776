module

public import Mathlib

@[expose] public section

/-! ### From `LSBA/Model/Basic.lean` -/

section

open MeasureTheory ProbabilityTheory Real Finset

open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Sample space of the `L` independent GUE blocks of size `W`, in real coordinates,
(1.2) [eq:covariance]. -/
abbrev Ω (W L : ℕ) : Type := Fin L × Fin W × Fin W → ℝ

/-- Product of standard real Gaussians on `Ω W L`. -/
def μ (W L : ℕ) : Measure (Ω W L) := Measure.pi fun _ => gaussianReal 0 1

instance (W L : ℕ) : IsProbabilityMeasure (μ W L) := by unfold μ; infer_instance

/-- Block `a` of the GUE matrix, (1.2) [eq:covariance]: diagonal `N(0,1/W)`, real and
imaginary parts of upper entries independent `N(0,1/(2W))`. -/
def gueBlock (W L : ℕ) (ω : Ω W L) (a : Fin L) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun α β =>
    if α = β then (ω (a, α, α) : ℂ) / Real.sqrt W
    else if α < β then ((ω (a, α, β) : ℂ) + Complex.I * ω (a, β, α)) / Real.sqrt (2 * W)
    else ((ω (a, β, α) : ℂ) - Complex.I * ω (a, α, β)) / Real.sqrt (2 * W)

/-- `A_L = S + S⁻¹` with `S` the cyclic shift of `ℤ_L`: `(A_L f)(a) = f(a+1) + f(a-1)`,
(1.3) [eq:model], for every `L`. -/
def cycleAdj (L : ℕ) : Matrix (Fin L) (Fin L) ℂ :=
  Matrix.of fun a b =>
    (if b.val = (a.val + 1) % L then 1 else 0) + (if a.val = (b.val + 1) % L then 1 else 0)

/-- Block-diagonal operator `diag(V_a : a ∈ ℤ_L)` on `ℂ^L ⊗ ℂ^W`. -/
def blockDiagOp {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then V p.1 p.2 q.2 else 0

/-- Deterministic block operator `(g A_L ⊗ I_W + diag V) / max{1,g}`, (1.3) [eq:model] and
(1.4) [eq:blockaction]. -/
def Hdet (g : ℝ) {W L : ℕ} (V : Fin L → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  ((max 1 g : ℝ)⁻¹ : ℂ) • ((g : ℂ) • (cycleAdj L ⊗ₖ (1 : Matrix (Fin W) (Fin W) ℂ)) +
    blockDiagOp V)

/-- The random model `H_{g,W,L}` of (1.3) [eq:model]. -/
def Hmat (g : ℝ) (W L : ℕ) (ω : Ω W L) : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ :=
  Hdet g (gueBlock W L ω)

end LSBA

end

end

/-! ### From `LSBA/Dyson/Scalar.lean` -/

section

open MeasureTheory Real Filter Topology Complex

open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- Right side of (1.9) [eq:dyson]. -/
def dysonRHS (g : ℝ) (z u : ℂ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ p in (-π)..π,
    ((2 * g * Real.cos p / max 1 g : ℝ) - z - u / ((max 1 g : ℝ) : ℂ) ^ 2)⁻¹

/-- `m_g(z)`: the unique solution in `ℂ_+` (junk value `0` if there is none). -/
def mDyson (g : ℝ) (z : ℂ) : ℂ :=
  if h : ∃! u : ℂ, 0 < u.im ∧ u = dysonRHS g z u then h.exists.choose else 0

end LSBA

end

end

/-! ### From `LSBA/Dyson/Stieltjes.lean` -/

section

open MeasureTheory Real Filter Topology Complex

open scoped ENNReal

noncomputable section

open scoped Classical

namespace LSBA

/-- Stieltjes transform `∫ (t - z)⁻¹ dν(t)`. -/
def stieltjes (ν : Measure ℝ) (z : ℂ) : ℂ := ∫ t, ((t : ℂ) - z)⁻¹ ∂ν

/-- `ν_g`: a probability measure with Stieltjes transform `m_g` on `ℂ_+` (junk `dirac 0`). -/
def nuDyson (g : ℝ) : Measure ℝ :=
  if h : ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ z : ℂ, 0 < z.im → stieltjes ν z = mDyson g z
  then h.choose else Measure.dirac 0

/-- `F_g(x) = ν_g((-∞, x])`, (1.10) [eq:distribution]. -/
def Fdist (g x : ℝ) : ℝ := (nuDyson g (Set.Iic x)).toReal

end LSBA

end

end

/-! ### From `LSBA/Spectral/Length.lean` -/

section

open MeasureTheory ProbabilityTheory Real Finset

open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- Cyclic interval `{x, …, x+r-1} ⊆ ℤ_N`. -/
def cycInterval (N : ℕ) (x : Fin N) (r : ℕ) : Finset (Fin N) :=
  univ.filter fun i => (i.val + N - x.val) % N < r

/-- Localization length of a mass profile `p : ℤ_N → ℝ`, (1.6) [eq:length]; the clause
`r = N` makes the value lie in `[1, N]` for every profile when `0 < N`. -/
def ellMass (N : ℕ) (p : Fin N → ℝ) : ℕ :=
  sInf {r : ℕ | 1 ≤ r ∧ r ≤ N ∧
    (r = N ∨ ∃ x : Fin N, (1 : ℝ) / 2 ≤ ∑ i ∈ cycInterval N x r, p i)}

/-- Localization length of a profile on `Fin L × Fin W`, through the coordinates (1.1) [eq:blocks].
-/
def ellProf (W L : ℕ) (p : Fin L × Fin W → ℝ) : ℕ :=
  ellMass (L * W) fun i => p (finProdFinEquiv.symm i)

end LSBA

end

end

/-! ### From `LSBA/Spectral/Counts.lean` -/

section

open MeasureTheory ProbabilityTheory Real Finset

open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Multiplicity of the eigenvalue `ev k`. -/
def mult (ev : n → ℝ) (k : n) : ℕ := #(univ.filter fun j => ev j = ev k)

/-- Diagonal of the spectral projection onto the eigenspace of `ev k`. -/
def projDiag (ev : n → ℝ) (v : n → n → ℂ) (k : n) (i : n) : ℝ :=
  ∑ j ∈ univ.filter (fun j => ev j = ev k), ‖v j i‖ ^ 2

/-- Number of eigenvalues (with multiplicity) in `J`. -/
def countIn (A : Matrix n n ℂ) (J : Set ℝ) : ℕ :=
  if hA : A.IsHermitian then #(univ.filter fun k => hA.eigenvalues k ∈ J) else 0

/-- Bad count: eigenvalues in `J` that are multiple, or simple with `ℓ < r`. -/
def badCount (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (J : Set ℝ) (r : ℝ) : ℕ :=
  if hA : A.IsHermitian then
    #(univ.filter fun k => hA.eigenvalues k ∈ J ∧
      (2 ≤ mult hA.eigenvalues k ∨
        ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ)
          : ℝ) < r))
  else 0

end LSBA

end

end

/-! ### From `LSBA/Model/Scales.lean` -/

section

open MeasureTheory ProbabilityTheory Real Finset

open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The uncapped scale `ℓ_{W,g} = max{W, W²g²}`, (1.7) [eq:scales]. -/
def ellScale (W : ℕ) (g : ℝ) : ℝ := max (W : ℝ) ((W : ℝ) ^ 2 * g ^ 2)

/-- The finite-volume scale `ℓ_{W,g,L} = min{WL, ℓ_{W,g}}`, (1.7) [eq:scales]. -/
def ellStar (W L : ℕ) (g : ℝ) : ℝ := min ((W : ℝ) * L) (ellScale W g)

end LSBA

end

end

/-! ### From `LSBA/Model/Bulk.lean` -/

section

open MeasureTheory ProbabilityTheory Real Finset

open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- The energy set `J_{g,κ,L}` of (1.16) [eq:bulk-sampling]; `L₀` stands for the threshold of
Lemma 1.3 [lem:rough-density]. -/
def bulkSet (g κ : ℝ) (L₀ L : ℕ) : Set ℝ :=
  if L < L₀ then Set.univ else {E | κ / 2 ≤ Fdist g (-|E|)}

end LSBA

end

end

/-! ### From `LSBA/Spectral/TwoSidedCounts.lean` -/

section

open MeasureTheory ProbabilityTheory Real Finset Filter

open scoped ENNReal NNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

/-- `B₊` of the proof of the upper bound in Theorem 1.4 [thm:main], before (3.11)
[uv:eq:upper-count]: eigenvalues in `J` that are multiple, or simple with `r < ℓ`. -/
def badCountUp (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (J : Set ℝ) (r : ℝ) :
    ℕ :=
  if hA : A.IsHermitian then
    #(univ.filter fun k => hA.eigenvalues k ∈ J ∧
      (2 ≤ mult hA.eigenvalues k ∨
        r < ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ)
          : ℝ)))
  else 0

/-- Two-sided good count: simple eigenvalues in `J` with `r ≤ ℓ ≤ R`. -/
def goodCountTwoSided (W L : ℕ) (A : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (J : Set ℝ)
    (r R : ℝ) : ℕ :=
  if hA : A.IsHermitian then
    #(univ.filter fun k => hA.eigenvalues k ∈ J ∧ mult hA.eigenvalues k = 1 ∧
      r ≤ ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ)
        : ℝ) ∧
      ((ellProf W L (projDiag hA.eigenvalues (fun j => ⇑(hA.eigenvectorBasis j)) k) : ℕ) : ℝ)
        ≤ R)
  else 0

end LSBA

end

end

