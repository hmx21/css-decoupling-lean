import Decoupling.HighDim.SchreyerFinalInput
import Decoupling.HighDim.SchreyerModelProfile

/-!
# HD014 Lemma 4: the actual bounded Schreyer CSS model

Only the original code and its topological condition are inputs. The
actual kernel resolutions, their free coordinates, and their length
bounds have all been constructed. The native profile retains all gluing
data, not just the dimensions of its individual layers.
-/
namespace Decoupling.HighDim.SchreyerCSS
open CategoryTheory CategoryTheory.Limits Matrix
noncomputable section
attribute [local instance] HasDerivedCategory.standard
variable {K : Type} [Field K] {D q s r : ℕ}
  (c : CSS.Checks K D q s r) (hc : c.Topological)

def model : CochainComplex (ModuleCat (Laurent K D)) ℤ := complex c (input c) hc

instance model_finite (j : ℤ) : Module.Finite (Laurent K D) ((model c hc).X j) :=
  complex_finite c (input c) hc j

instance model_free (j : ℤ) : Module.Free (Laurent K D) ((model c hc).X j) :=
  complex_free c (input c) hc j

instance model_isGE : (model c hc).IsGE 1 := complex_isGE c (input c) hc

instance model_boundedBelow : (model c hc).IsStrictlyGE (-((D+2 : ℕ) : ℤ)) :=
  complex_boundedBelow c (input c) hc

theorem model_boundedAbove (hD : 1 ≤ D) : (model c hc).IsStrictlyLE ((D : ℤ)+2) :=
  complex_boundedAbove c (input c) hc hD

theorem model_support (hD : 2 ≤ D) (j : ℤ) (hj : (D : ℤ)+2 < |j|) :
    IsZero ((model c hc).X j) := by
  by_cases hn : j < 0
  · have hneg : j < -((D+2 : ℕ) : ℤ) := by rw [abs_of_neg hn] at hj; omega
    exact (model c hc).isZero_of_isStrictlyGE (-((D+2 : ℕ) : ℤ)) j hneg
  · have hpos : (D : ℤ)+2 < j := by rw [abs_of_nonneg (by omega)] at hj; exact hj
    let : (model c hc).IsStrictlyLE ((D : ℤ)+2) := model_boundedAbove c hc (by omega)
    exact (model c hc).isZero_of_isStrictlyLE ((D : ℤ)+2) j hpos

theorem model_exact_nonpositive (j : ℤ) (hj : j ≤ 0) : (model c hc).ExactAt j :=
  (model c hc).exactAt_of_isGE 1 j (by omega)

def model_profileIso : DerivedCategory.Q.obj (model c hc) ≅ Profile.S_X c :=
  complex_profileIso c (input c) hc

def model_positiveHomologyEquivExt (n : ℕ) :
    (model c hc).homology (n+1 : ℕ) ≃ₗ[Laurent K D] Layers.E_X c (n+1) :=
  complex_positiveHomologyEquivExt c (input c) hc n

theorem model_Z_window (x : CSS.Free K D r) :
    zeroCoordinates c (input c) ((model c hc).d (-1) 0 x) = dagger c.H_Z *ᵥ x :=
  complex_Z_window c (input c) hc x

theorem model_X_window (x : (model c hc).X 0) :
    oneCoordinates c (input c) ((model c hc).d 0 1 x) =
      c.H_X *ᵥ zeroCoordinates c (input c) x :=
  complex_X_window c (input c) hc x

theorem model_gamma_window (x : (model c hc).X 1) :
    twoCoordinates c (input c) ((model c hc).d 1 2 x) =
      (input c).gamma *ᵥ oneCoordinates c (input c) x :=
  complex_gamma_window c (input c) hc x

/-- Complete bounded-model conclusion with no intermediate tail assumption. -/
theorem lemma4 (hD : 2 ≤ D) :
    (∀ j, Module.Finite (Laurent K D) ((model c hc).X j)) ∧
    (∀ j, Module.Free (Laurent K D) ((model c hc).X j)) ∧
    (∀ j, (D : ℤ)+2 < |j| → IsZero ((model c hc).X j)) ∧
    (∀ j, j ≤ 0 → (model c hc).ExactAt j) ∧
    (∀ n : ℕ, Nonempty ((model c hc).homology (n+1 : ℕ) ≃ₗ[Laurent K D] Layers.E_X c (n+1))) ∧
    Nonempty (DerivedCategory.Q.obj (model c hc) ≅ Profile.S_X c) :=
  ⟨model_finite c hc,model_free c hc,model_support c hc hD,model_exact_nonpositive c hc,
    fun n => ⟨model_positiveHomologyEquivExt c hc n⟩,⟨model_profileIso c hc⟩⟩

end
end Decoupling.HighDim.SchreyerCSS
