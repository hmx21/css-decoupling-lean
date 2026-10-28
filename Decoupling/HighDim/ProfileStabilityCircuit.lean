import Decoupling.HighDim.ProfileStabilityAncilla
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Lemma 5 for actual Clifford actions and SUM/SWAP words

An invertible action on physical X representatives, together with its actual
stabilizer-image equality, induces an isomorphism of the reduced quotients.
This is the CSS-preserving Clifford hypothesis used in the manuscript.
For the project's physical SUM/SWAP words, invertibility is proved from the
already established pairing identity; it is not an additional input.
-/

namespace Decoupling.HighDim.ProfileStability

open CategoryTheory CategoryTheory.Abelian Matrix
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [CommRing K] {D : ℕ}
local notation "R" => Laurent K D
variable {Q Q' C C' : Type} [Fintype C] [Fintype C']

/-- Transport of the literal X-stabilizer submodule descends to the quotient. -/
def reducedIsoOfXTransport (H : Matrix C Q R) (H' : Matrix C' Q' R)
    (U : (Q → R) ≃ₗ[R] (Q' → R))
    (h : ∀ v, (∃ z, U (dagger H *ᵥ z) = v) ↔ ∃ z, dagger H' *ᵥ z = v) :
    matrixReduced H ≅ matrixReduced H' := by
  apply LinearEquiv.toModuleIso
  apply Submodule.Quotient.equiv _ _ U
  ext v
  constructor
  · rintro ⟨w, ⟨z, hz⟩, hw⟩
    exact (h v).mp ⟨z, by rw [← hz] at hw; exact hw⟩
  · intro hv
    obtain ⟨z, hz⟩ := (h v).mpr hv
    exact ⟨dagger H *ᵥ z, ⟨z, rfl⟩, hz⟩

/-- The entire profile is invariant under a CSS-preserving invertible X action. -/
def profileIsoOfXTransport (H : Matrix C Q R) (H' : Matrix C' Q' R)
    (U : (Q → R) ≃ₗ[R] (Q' → R))
    (h : ∀ v, (∃ z, U (dagger H *ᵥ z) = v) ↔ ∃ z, dagger H' *ᵥ z = v) :
    matrixProfile H ≅ matrixProfile H' :=
  moduleProfileIso (reducedIsoOfXTransport H H' U h)

/-- Relabel physical species, preserving their Laurent coefficients. -/
def speciesEquiv (e : Q ≃ Q') : (Q → R) ≃ₗ[R] (Q' → R) where
  toFun v := v ∘ e.symm
  invFun v := v ∘ e
  left_inv v := by funext q; simp
  right_inv v := by funext q; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Fintype Q'] [DecidableEq Q']

/-- The actual X word is invertible: its inverse is the dagger of the Z word. -/
def wordXEquiv (gates : List (Circuit.Layer K D Q')) : (Q' → R) ≃ₗ[R] (Q' → R) := by
  have hleft : dagger (Circuit.wordZ gates) * Circuit.wordX gates = 1 := by
    simpa only [dagger_mul, dagger_dagger, dagger_one] using
      congrArg dagger (Circuit.word_preserves_pairing gates)
  have hright : Circuit.wordX gates * dagger (Circuit.wordZ gates) = 1 :=
    mul_eq_one_comm.mp hleft
  exact {
    (Circuit.wordX gates).mulVecLin with
    invFun := (dagger (Circuit.wordZ gates)).mulVec
    left_inv v := by change dagger (Circuit.wordZ gates) *ᵥ (Circuit.wordX gates *ᵥ v) = v
                     rw [mulVec_mulVec, hleft, one_mulVec]
    right_inv v := by change Circuit.wordX gates *ᵥ (dagger (Circuit.wordZ gates) *ᵥ v) = v
                      rw [mulVec_mulVec, hright, one_mulVec] }

@[simp] theorem wordXEquiv_apply (gates : List (Circuit.Layer K D Q')) (v : Q' → R) :
    wordXEquiv gates v = Circuit.wordX gates *ᵥ v := rfl

variable {Z Z' : Type} [Fintype Z] [Fintype Z'] [Fintype Q] [DecidableEq Q]

/-- A physical word carrying both actual stabilizer images induces full profile invariance. -/
def circuitProfileIso (gates : List (Circuit.Layer K D Q')) (e : Q ≃ Q')
    (HC : Matrix C Q R) (HT : Matrix C' Q' R)
    (BC : Matrix Q Z R) (BT : Matrix Q' Z' R)
    (h : PhysicalIsomorphism.Transports gates e HC HT BC BT) :
    matrixProfile HC ≅ matrixProfile HT :=
  profileIsoOfXTransport HC HT ((speciesEquiv e).trans (wordXEquiv gates)) h.2

/-- Invariance on the actual `CSS.Checks` profile objects. -/
def cssCircuitProfileIso {q s r q' s' r' : ℕ}
    (c : CSS.Checks K D q s r) (d : CSS.Checks K D q' s' r')
    (gates : List (Circuit.Layer K D (Fin q'))) (e : Fin q ≃ Fin q')
    (h : PhysicalIsomorphism.Transports gates e c.H_X d.H_X
      (dagger c.H_Z) (dagger d.H_Z)) :
    Profile.S_X c ≅ Profile.S_X d :=
  circuitProfileIso gates e c.H_X d.H_X (dagger c.H_Z) (dagger d.H_Z) h

/-- The dual sector is transported by the Fourier-conjugate physical word. -/
def cssCircuitZProfileIso {q s r q' s' r' : ℕ}
    (c : CSS.Checks K D q s r) (d : CSS.Checks K D q' s' r')
    (gates : List (Circuit.Layer K D (Fin q'))) (e : Fin q ≃ Fin q')
    (h : PhysicalIsomorphism.Transports gates e c.H_X d.H_X
      (dagger c.H_Z) (dagger d.H_Z)) :
    Profile.S_Z c ≅ Profile.S_Z d := by
  apply cssCircuitProfileIso c.swap d.swap (gates.map Circuit.fourierDual) e
  simpa only [dagger_dagger, CSS.Checks.swap] using
    PhysicalIsomorphism.transports_fourierDual gates e c.H_X d.H_X
      (dagger c.H_Z) (dagger d.H_Z) h

/-- The X action of a CSS-preserving Clifford with Z matrices `W` and `W⁻¹`.
The two inverse equalities are the definition of this ambient physical action;
no quotient or derived isomorphism is an input. -/
def cliffordXEquiv (W : Matrix Q' Q R) (V : Matrix Q Q' R)
    (hWV : W * V = 1) (hVW : V * W = 1) : (Q → R) ≃ₗ[R] (Q' → R) := by
  have hl : dagger W * dagger V = 1 := by rw [← dagger_mul, hVW, dagger_one]
  have hr : dagger V * dagger W = 1 := by rw [← dagger_mul, hWV, dagger_one]
  exact {
    (dagger V).mulVecLin with
    invFun := (dagger W).mulVec
    left_inv v := by change dagger W *ᵥ (dagger V *ᵥ v) = v
                     rw [mulVec_mulVec, hl, one_mulVec]
    right_inv v := by change dagger V *ᵥ (dagger W *ᵥ v) = v
                      rw [mulVec_mulVec, hr, one_mulVec] }

/-- Lemma 5 for every invertible CSS-preserving Laurent Clifford action,
including actions beyond the project's explicit SUM/SWAP gate set. -/
def cliffordProfileIso (H : Matrix C Q R) (H' : Matrix C' Q' R)
    (W : Matrix Q' Q R) (V : Matrix Q Q' R)
    (hWV : W * V = 1) (hVW : V * W = 1)
    (hX : ∀ v, (∃ z, dagger V *ᵥ (dagger H *ᵥ z) = v) ↔
      ∃ z, dagger H' *ᵥ z = v) : matrixProfile H ≅ matrixProfile H' :=
  profileIsoOfXTransport H H' (cliffordXEquiv W V hWV hVW) hX

end
end Decoupling.HighDim.ProfileStability
