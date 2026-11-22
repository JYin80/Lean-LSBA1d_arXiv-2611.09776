module

public import LSBA.Dyson.Distribution
public import LSBA.MainDefs

@[expose] public section

/-!
# The selected energy set

The energy set `J_{g,κ,L}` of (1.16) [eq:bulk-sampling], with the threshold `L_{κ/2}` of
Lemma 1.3 [lem:rough-density] as a parameter.
-/

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal Kronecker Matrix

noncomputable section

open scoped Classical

namespace LSBA

theorem measurableSet_bulkSet (g κ : ℝ) (L₀ L : ℕ) : MeasurableSet (bulkSet g κ L₀ L) := by
  unfold bulkSet
  split_ifs with h
  · exact MeasurableSet.univ
  · have hm : Measurable fun E : ℝ => Fdist g (-|E|) :=
      (Fdist_monotone g).measurable.comp (continuous_abs.neg.measurable)
    exact hm measurableSet_Ici

end LSBA
