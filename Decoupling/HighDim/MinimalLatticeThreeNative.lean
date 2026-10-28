import Decoupling.HighDim.MinimalLatticeThreeIndex
import Decoupling.HighDim.ExtValuesAlternating

/-!
# Three-dimensional minimization for genuine Ext² classes

Source: Corollary 2, HD008. The alternating form is obtained from native
derived Ext, and its three coefficients are its actual plaquette values.
The separate restriction comparison identifies latticewise vanishing
with vanishing of scalar restriction.
-/

namespace Decoupling.HighDim.MinimalLattice.Three
open CategoryTheory CategoryTheory.Abelian
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

def basisVector (i : Fin 3) : V (K := K) := Pi.single i 1

/-- Plaquette values in orientation order 01, 02, 12. -/
def coefficients (f : AlternatingMap K (V (K := K)) M (Fin 2)) : Fin 3 → M :=
  ![f ![basisVector 0, basisVector 1], f ![basisVector 0, basisVector 2],
    f ![basisVector 1, basisVector 2]]

theorem form_coefficients (f : AlternatingMap K (V (K := K)) M (Fin 2)) :
    form (coefficients f) = f := by
  apply sub_eq_zero.mp
  apply (ExtValues.alternating_eq_zero_iff_cell_values _).mpr
  intro I
  have hi : I 0 < I 1 := I.strictMono (by decide)
  have hv : (fun i => Pi.single (I i) (1 : K)) =
      ![basisVector (I 0), basisVector (I 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [AlternatingMap.sub_apply, form_pair]
  generalize h0 : I 0 = a at *
  generalize h1 : I 1 = b at *
  fin_cases a <;> fin_cases b <;>
    simp_all [evaluate, minors, coefficients, basisVector, Fin.sum_univ_succ]

theorem alternating_pair_formula (f : AlternatingMap K (V (K := K)) M (Fin 2))
    (u v : V (K := K)) : f ![u, v] = evaluate (coefficients f) u v := by
  rw [← form_pair, form_coefficients]

theorem alternating_vanishes_iff (f : AlternatingMap K (V (K := K)) M (Fin 2))
    (W : Submodule K (V (K := K))) :
    (∀ v : Fin 2 → V (K := K), (∀ i, v i ∈ W) → f v = 0) ↔
      Isotropic (coefficients f) W := by
  constructor
  · intro h u hu v hv
    rw [← alternating_pair_formula]
    exact h ![u, v] (by intro i; fin_cases i <;> assumption)
  · intro h v hv
    have he : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [he, alternating_pair_formula]
    exact h _ (hv 0) _ (hv 1)

section Native
variable {p : ℕ} [Fact p.Prime]
  (B A : ModuleCat (Laurent (ZMod p) 3))
  [FiniteDimensional (ZMod p) (Layers.coefficients B)]
  (hB : TrivialLayers.AugmentationAction B) (hA : TrivialLayers.AugmentationAction A)
  (κ : Ext B A 2)

def nativeCoefficients : Fin 3 → (Layers.coefficients B →ₗ[ZMod p] Layers.coefficients A) :=
  coefficients (ExtValues.nativeAlternatingEquiv B A hB hA 2 κ)

/-- Exact minimum for vanishing of the genuine native Ext² alternating form. -/
theorem nativeMinimumIndex_classification :
    IsLeast {n : ℕ | ∃ Γ : AddSubgroup (Translation 3), Γ.FiniteIndex ∧
      (∀ v : Fin 2 → Residue p 3, (∀ i, v i ∈ image p 3 Γ) →
        ExtValues.nativeAlternatingEquiv B A hB hA 2 κ v = 0) ∧ Γ.index = n}
      (if ∀ i, nativeCoefficients B A hB hA κ i = 0 then 1 else
        if LinearIndependent (ZMod p) (nativeCoefficients B A hB hA κ) then p ^ 2 else p) := by
  simp only [alternating_vanishes_iff]
  exact minimumIndex_classification (nativeCoefficients B A hB hA κ)

end Native
end
end Decoupling.HighDim.MinimalLattice.Three
