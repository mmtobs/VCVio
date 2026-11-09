/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Finite telescopes of returned event masses

Cancellation-free telescopes, finite averaging, and integration preserve the native
subprobability interpretation of adaptive Boolean experiments.
-/

public section

namespace GXMSS.Reductions.HybridTelescope
open ENNReal OracleComp OracleSpec

/-- A cancellation-free finite telescope suitable for subprobability event masses. -/
theorem finite_chain_hybrid_telescope (f : ℕ → ℝ≥0∞) (n : ℕ) :
    f 0 + ∑ j ∈ Finset.range n, f (j + 1) =
      f n + ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    rw [← add_assoc, ih]
    ac_rfl
/-- A finite additive telescope yields the desired loss from one Boolean UD distance. -/
theorem finite_hybrid_boolDist_bound
    (source terminal real ideal distance : ℝ≥0∞) (n : ℕ)
    (hfinite : (n : ℝ≥0∞) * ideal ≠ ∞)
    (htelescope : source + (n : ℝ≥0∞) * ideal =
      terminal + (n : ℝ≥0∞) * real)
    (hdistance : real ≤ ideal + distance) :
    source ≤ terminal + (n : ℝ≥0∞) * distance := by
  apply ENNReal.le_of_add_le_add_right hfinite
  calc
    source + (n : ℝ≥0∞) * ideal =
        terminal + (n : ℝ≥0∞) * real := htelescope
    _ ≤ terminal + (n : ℝ≥0∞) * (ideal + distance) := by
      gcongr
    _ = (terminal + (n : ℝ≥0∞) * distance) +
        (n : ℝ≥0∞) * ideal := by
      rw [mul_add]
      ac_rfl
/-- A uniform finite hybrid index averages unconditioned returned true masses. -/
theorem uniform_fin_bind_true_mass (n : ℕ) [NeZero n]
    (f : Fin n → ProbComp Bool) :
    𝒟[($ᵗ (Fin n) : ProbComp (Fin n)) >>= f] {true} =
      (n : ℝ≥0∞)⁻¹ * ∑ j : Fin n, 𝒟[f j] {true} := by
  rw [evalDist_bind_of_discrete, SampleableType.evalDist_uniformSample,
    ProbabilityTheory.uniformOn_univ_bind_apply (fun j => 𝒟[f j]) {true}
      (measurableSet_singleton true)]
  simp only [Fintype.card_fin, Finset.mul_sum]
/-- Zeroing all hybrid indices beyond a selected cut leaves its finite prefix sum. -/
theorem fin_sum_lt_eq_range (n g : ℕ) (hg : g ≤ n)
    (f : ℕ → ℝ≥0∞) :
    (∑ j : Fin n, if j.val < g then f j.val else 0) =
      ∑ j ∈ Finset.range g, f j := by
  change (∑ j : Fin n, (fun k : ℕ => if k < g then f k else 0) j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < g then f k else 0) n]
  have hsum := Finset.sum_range_add_sum_Ico
    (fun j : ℕ => if j < g then f j else 0) hg
  rw [← hsum]
  have hprefix : (∑ j ∈ Finset.range g, if j < g then f j else 0) =
      ∑ j ∈ Finset.range g, f j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj]
  have htail : (∑ j ∈ Finset.Ico g n, if j < g then f j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [not_lt.mpr (Finset.mem_Ico.mp hj).1]
  rw [hprefix, htail, add_zero]
/-- Pointwise selected-cut masses average to the exact finite-prefix sum. -/
theorem uniform_fin_prefix_true_mass_of_pointwise
    (n g : ℕ) [NeZero n] (hg : g ≤ n)
    (actual : Fin n → ProbComp Bool) (f : ℕ → ℝ≥0∞)
    (hpoint : ∀ j : Fin n,
      𝒟[actual j] {true} = if j.val < g then f j.val else 0) :
    𝒟[do let j ← ($ᵗ (Fin n) : ProbComp (Fin n)); actual j] {true} =
      (n : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range g, f j := by
  rw [uniform_fin_bind_true_mass]
  simp_rw [hpoint]
  exact congrArg ((n : ℝ≥0∞)⁻¹ * ·) (fin_sum_lt_eq_range n g hg f)
/-- A finite additive telescope is unchanged by exact averaging over a nonempty index domain. -/
theorem finite_chain_hybrid_mean_telescope (real ideal : ℕ → ℝ≥0∞)
    (n g : ℕ) [NeZero n]
    (htelescope : real 0 + ∑ j ∈ Finset.range g, ideal j =
      real g + ∑ j ∈ Finset.range g, real j) :
    real 0 + (n : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹ *
      ∑ j ∈ Finset.range g, ideal j) =
    real g + (n : ℝ≥0∞) * ((n : ℝ≥0∞)⁻¹ *
      ∑ j ∈ Finset.range g, real j) := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (NeZero.ne n)
  have hntop : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
  simpa only [← mul_assoc, ENNReal.mul_inv_cancel hn0 hntop, one_mul] using htelescope

/-- Pointwise additive mass identities integrate over a common outer draw. -/
theorem bind_true_mass_telescope {α : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (draw : ProbComp α)
    (source ideal terminal real : α → ProbComp Bool) (n : ℕ)
    (h : ∀ a,
      𝒟[source a] {true} + (n : ℝ≥0∞) * 𝒟[ideal a] {true} =
        𝒟[terminal a] {true} + (n : ℝ≥0∞) * 𝒟[real a] {true}) :
    𝒟[draw >>= source] {true} + (n : ℝ≥0∞) * 𝒟[draw >>= ideal] {true} =
      𝒟[draw >>= terminal] {true} + (n : ℝ≥0∞) * 𝒟[draw >>= real] {true} := by
  simp only [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (measurableSet_singleton true)
      Measurable.of_discrete.aemeasurable]
  rw [← MeasureTheory.lintegral_const_mul _ (Measurable.of_discrete :
      Measurable fun a : α => 𝒟[ideal a] {true}),
    ← MeasureTheory.lintegral_add_left (Measurable.of_discrete :
      Measurable fun a : α => 𝒟[source a] {true})]
  rw [← MeasureTheory.lintegral_const_mul _ (Measurable.of_discrete :
      Measurable fun a : α => 𝒟[real a] {true}),
    ← MeasureTheory.lintegral_add_left (Measurable.of_discrete :
      Measurable fun a : α => 𝒟[terminal a] {true})]
  exact MeasureTheory.lintegral_congr fun a => h a

/-- Local adjacent-hybrid equalities imply the cancellation-free finite telescope. -/
theorem finite_hybrid_telescope_of_step (real ideal : ℕ → ℝ≥0∞) (g : ℕ)
    (hstep : ∀ j, j < g → ideal j = real (j + 1)) :
    real 0 + ∑ j ∈ Finset.range g, ideal j =
      real g + ∑ j ∈ Finset.range g, real j := by
  have hsum : (∑ j ∈ Finset.range g, ideal j) =
      ∑ j ∈ Finset.range g, real (j + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hstep j (Finset.mem_range.mp hj)
  rw [hsum]
  exact finite_chain_hybrid_telescope real g

/-- Exact finite averaging transports a proved finite telescope to the actual selected programs.
Indices outside the prefix must have zero returned winning mass. -/
theorem selected_true_mass_telescope (real ideal : ℕ → ℝ≥0∞) (n g : ℕ) [NeZero n]
    (hg : g ≤ n) (selectedReal selectedIdeal : Fin n → ProbComp Bool)
    (hreal : ∀ j, 𝒟[selectedReal j] {true} = if j.val < g then real j.val else 0)
    (hideal : ∀ j, 𝒟[selectedIdeal j] {true} = if j.val < g then ideal j.val else 0)
    (htelescope : real 0 + ∑ j ∈ Finset.range g, ideal j =
      real g + ∑ j ∈ Finset.range g, real j) :
    real 0 + (n : ℝ≥0∞) *
        𝒟[($ᵗ (Fin n) : ProbComp (Fin n)) >>= selectedIdeal] {true} =
      real g + (n : ℝ≥0∞) *
        𝒟[($ᵗ (Fin n) : ProbComp (Fin n)) >>= selectedReal] {true} := by
  rw [uniform_fin_prefix_true_mass_of_pointwise n g hg selectedIdeal ideal hideal,
    uniform_fin_prefix_true_mass_of_pointwise n g hg selectedReal real hreal]
  exact finite_chain_hybrid_mean_telescope real ideal n g htelescope

/-- One-step equalities of returned event masses telescope under the actual uniform cut sampler.
The inactive cut coordinates return false rather than conditioning the sampler. -/
theorem uniform_prefix_true_mass_telescope (real ideal : ℕ → ProbComp Bool)
    (n g : ℕ) [NeZero n] (hg : g ≤ n)
    (hstep : ∀ j, j < g → 𝒟[ideal j] {true} = 𝒟[real (j + 1)] {true}) :
    𝒟[real 0] {true} + (n : ℝ≥0∞) * 𝒟[do
      let j ← ($ᵗ (Fin n) : ProbComp (Fin n))
      if j.val < g then ideal j.val else pure false] {true} =
    𝒟[real g] {true} + (n : ℝ≥0∞) * 𝒟[do
      let j ← ($ᵗ (Fin n) : ProbComp (Fin n))
      if j.val < g then real j.val else pure false] {true} := by
  apply selected_true_mass_telescope (fun j => 𝒟[real j] {true})
    (fun j => 𝒟[ideal j] {true}) n g hg
  · intro j
    by_cases hj : j.val < g <;> simp [hj]
  · intro j
    by_cases hj : j.val < g <;> simp [hj]
  · exact finite_hybrid_telescope_of_step (fun j => 𝒟[real j] {true})
      (fun j => 𝒟[ideal j] {true}) g hstep

end GXMSS.Reductions.HybridTelescope
