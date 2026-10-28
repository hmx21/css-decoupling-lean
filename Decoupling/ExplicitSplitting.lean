import Decoupling.Comparison
import Decoupling.ZeroComparison
import Decoupling.Normalization

/-!
# The corrected lift and explicit augmentation isomorphism

This file formalizes the retraction-based construction in Proposition C.1.
In characteristic two the correction is `n ↦ n + ι(p(n))`. It annihilates
the first layer and descends through `π` to a section. The resulting actual
linear equivalence is `β(e,l) = ι(e) + σ(l)`, with inverse `(p,π)`.
-/

universe u

namespace Decoupling.ExplicitSplitting

open Module Matrix EvaluationLinear

noncomputable section

variable (A E N L : Type u) [CommRing A]
  [AddCommGroup E] [Module A E]
  [AddCommGroup N] [Module A N]
  [AddCommGroup L] [Module A L]

/-- An exact module sequence with a supplied retraction onto its first term.
The section of the last map is a conclusion of the construction. -/
structure RetractionData where
  ι : E →ₗ[A] N
  π : N →ₗ[A] L
  p : N →ₗ[A] E
  exact : LinearMap.range ι = LinearMap.ker π
  surjective : Function.Surjective π
  retract : p.comp ι = LinearMap.id

namespace RetractionData

variable {A E N L}
variable (r : RetractionData A E N L)

@[simp] theorem p_ι (e : E) : r.p (r.ι e) = e := DFunLike.congr_fun r.retract e

@[simp] theorem π_ι (e : E) : r.π (r.ι e) = 0 := by
  have h : r.ι e ∈ LinearMap.range r.ι := ⟨e, rfl⟩
  rw [r.exact] at h
  exact h

theorem zero_of_π_p_zero (n : N) (hπ : r.π n = 0) (hp : r.p n = 0) : n = 0 := by
  have hn : n ∈ LinearMap.range r.ι := by rw [r.exact]; exact hπ
  obtain ⟨e, rfl⟩ := hn
  have he : e = 0 := (r.p_ι e).symm.trans hp
  rw [he, map_zero]

/-- The characteristic-two corrected representative. -/
def correction : N →ₗ[A] N := LinearMap.id + r.ι.comp r.p

@[simp] theorem correction_apply (n : N) : r.correction n = n + r.ι (r.p n) := rfl

@[simp] theorem π_correction (n : N) : r.π (r.correction n) = r.π n := by
  simp [correction]

variable [CharP A 2]

@[simp] theorem p_correction (n : N) : r.p (r.correction n) = 0 := by
  simp only [correction_apply, map_add, r.p_ι]
  exact Comparison.module_add_self (A := A) E _

theorem correction_zero_of_π_zero (n : N) (hn : r.π n = 0) :
    r.correction n = 0 :=
  r.zero_of_π_p_zero _ (by rw [r.π_correction, hn]) (r.p_correction n)

/-- The correction descends through `π`; no section is assumed. -/
theorem exists_section : ∃ σ : L →ₗ[A] N, σ.comp r.π = r.correction := by
  apply ZeroComparison.exists_descend_of_surjective r.π r.surjective r.correction
  intro n hn
  exact r.correction_zero_of_π_zero n hn

def σ : L →ₗ[A] N := Classical.choose r.exists_section

theorem σ_comp_π : r.σ.comp r.π = r.correction := Classical.choose_spec r.exists_section

@[simp] theorem σ_π (n : N) : r.σ (r.π n) = r.correction n :=
  DFunLike.congr_fun r.σ_comp_π n

@[simp] theorem π_σ (l : L) : r.π (r.σ l) = l := by
  obtain ⟨n, rfl⟩ := r.surjective l
  rw [r.σ_π, r.π_correction]

@[simp] theorem p_σ (l : L) : r.p (r.σ l) = 0 := by
  obtain ⟨n, rfl⟩ := r.surjective l
  rw [r.σ_π, r.p_correction]

/-- The actual augmentation isomorphism, directed from the standard sum to `N`. -/
def β : (E × L) ≃ₗ[A] N :=
  LinearEquiv.ofLinearMap (r.ι.coprod r.σ) (r.p.prod r.π)
    (by
      ext n
      change r.ι (r.p n) + r.σ (r.π n) = n
      rw [r.σ_π, r.correction_apply, add_left_comm,
        Comparison.module_add_self (A := A) N, add_zero])
    (by
      apply LinearMap.ext
      intro z
      apply Prod.ext
      · change r.p (r.ι z.1 + r.σ z.2) = z.1
        simp
      · change r.π (r.ι z.1 + r.σ z.2) = z.2
        simp)

@[simp] theorem β_apply (e : E) (l : L) : r.β (e, l) = r.ι e + r.σ l := rfl

@[simp] theorem β_symm_apply (n : N) : r.β.symm n = (r.p n, r.π n) := rfl

variable {B : Type u} [AddCommGroup B] [Module A B]

/-- Correct an arbitrary lift without changing its projection onto `L`. -/
def correctedLift (V : B →ₗ[A] N) : B →ₗ[A] N := r.correction.comp V

omit [CharP A 2] in
theorem correctedLift_formula (V : B →ₗ[A] N) :
    r.correctedLift V = V + r.ι.comp (r.p.comp V) := by ext b; rfl

theorem correctedLift_kills_kernel (V : B →ₗ[A] N) (b₁ : B →ₗ[A] L)
    (hV : r.π.comp V = b₁) :
    LinearMap.ker b₁ ≤ LinearMap.ker (r.correctedLift V) := by
  intro b hb
  apply r.correction_zero_of_π_zero
  have h := DFunLike.congr_fun hV b
  exact h.trans hb

/-- The corrected lift is the section evaluated on the original presentation. -/
theorem correctedLift_descends (V : B →ₗ[A] N) (b₁ : B →ₗ[A] L)
    (hV : r.π.comp V = b₁) : r.σ.comp b₁ = r.correctedLift V := by
  ext b
  have hb : r.π (V b) = b₁ b := DFunLike.congr_fun hV b
  change r.σ (b₁ b) = r.correction (V b)
  rw [← hb, r.σ_π]

end RetractionData

section Syndrome

variable {A E N L}
  {P F Q : Type u} [AddCommGroup P] [Module A P]
  [AddCommGroup F] [Module A F] [AddCommGroup Q] [Module A Q]

/-- Turn the actual syndrome sequence and a chosen layer identification into
retraction data. Exactness is proved by `Syndrome`, not assumed again. -/
def ofSyndrome (c : Syndrome.Cochain A P F Q) (e : E ≃ₗ[A] c.C1)
    (p : c.N →ₗ[A] E) (hp : p.comp (c.ι.comp e.toLinearMap) = LinearMap.id) :
    RetractionData A E c.N c.L where
  ι := c.ι.comp e.toLinearMap
  π := c.π
  p := p
  exact := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
    exact c.first_shortExact.exact.moduleCat_range_eq_ker
  surjective := c.π_surjective
  retract := hp

end Syndrome

section Matrices

variable {q s k t n m : ℕ}
variable (c : Syndrome.Cochain R (Fin q → R) (Fin s → R) (Fin k → R))
variable (r : RetractionData R (Trivial t) c.N c.L)

/-- The constant matrix representing the given retraction on free representatives. -/
def retractionMatrix : Matrix (Fin t) (Fin s) (ZMod 2) :=
  coefficientMatrix (r.p.comp c.ε)

theorem retractionMatrix_eval :
    evalMatrix (retractionMatrix c r) = r.p.comp c.ε :=
  evalMatrix_coefficientMatrix _

/-- Representatives `T` of the first-layer inclusion always exist: the source
is finite free and the quotient map to the syndrome module is onto. -/
theorem exists_T : ∃ T : Matrix (Fin s) (Fin t) R,
    ∀ a : Fin t → R, c.ε (T *ᵥ a) = r.ι (augmentation ∘ a) := by
  obtain ⟨T, hT⟩ := Module.projective_lifting_property c.ε
    (r.ι.comp (evalMatrix (1 : Matrix (Fin t) (Fin t) (ZMod 2))))
    (LinearMap.range c.d₁).mkQ_surjective
  refine ⟨LinearMap.toMatrix' T, ?_⟩
  intro a
  rw [LinearMap.toMatrix'_mulVec]
  simpa only [LinearMap.comp_apply, evalMatrix_apply, one_mulVec] using
    DFunLike.congr_fun hT a

/-- Each column of a presentation of `L=range γ` has a free representative `V`. -/
theorem exists_V (b₁ : (Fin n → R) →ₗ[R] c.L) :
    ∃ V : Matrix (Fin s) (Fin n) R,
      ∀ w : Fin n → R, c.π (c.ε (V *ᵥ w)) = b₁ w := by
  obtain ⟨V, hV⟩ := Module.projective_lifting_property c.γ.rangeRestrict b₁
    c.γ.surjective_rangeRestrict
  refine ⟨LinearMap.toMatrix' V, ?_⟩
  intro w
  rw [LinearMap.toMatrix'_mulVec, c.π_mk]
  exact DFunLike.congr_fun hV w

/-- Equation (C2), with the constant product embedded back into the Laurent ring. -/
def correctedMatrix (T : Matrix (Fin s) (Fin t) R)
    (C : Matrix (Fin t) (Fin s) (ZMod 2)) (V : Matrix (Fin s) (Fin n) R) :
    Matrix (Fin s) (Fin n) R := V + T * (C * atOne V).map constant

theorem evaluate_constant_mulVec (D : Matrix (Fin t) (Fin n) (ZMod 2))
    (w : Fin n → R) :
    augmentation ∘ (D.map constant *ᵥ w) = D *ᵥ (augmentation ∘ w) := by
  have h : (D.map constant).map augmentation = D := by ext i j; simp
  funext i
  exact (augmentation.map_mulVec (D.map constant) w i).trans (by rw [h])

/-- The displayed Laurent-matrix correction represents exactly `V+ιpV` in `N`. -/
theorem correctedMatrix_class
    (T : Matrix (Fin s) (Fin t) R) (V : Matrix (Fin s) (Fin n) R)
    (hT : ∀ a : Fin t → R, c.ε (T *ᵥ a) = r.ι (augmentation ∘ a))
    (w : Fin n → R) :
    c.ε (correctedMatrix T (retractionMatrix c r) V *ᵥ w) =
      r.correction (c.ε (V *ᵥ w)) := by
  rw [correctedMatrix, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, map_add, hT,
    evaluate_constant_mulVec]
  change c.ε (V *ᵥ w) + r.ι (evalMatrix (retractionMatrix c r * atOne V) w) = _
  rw [← evalMatrix_mulVec, retractionMatrix_eval]
  rfl

/-- The canonical retraction matrix kills the evaluated boundary matrix. -/
theorem retractionMatrix_boundary :
    retractionMatrix c r * atOne (LinearMap.toMatrix' c.d₁) = 0 := by
  apply (evalMatrix_eq_zero_iff _).mp
  apply LinearMap.ext
  intro v
  rw [← evalMatrix_mulVec, retractionMatrix_eval, LinearMap.toMatrix'_mulVec]
  change r.p (c.ε (c.d₁ v)) = 0
  have hv : c.ε (c.d₁ v) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩
  rw [hv, map_zero]

/-- The second finite splitting-certificate equation follows from the actual retraction. -/
theorem retractionMatrix_T (T : Matrix (Fin s) (Fin t) R)
    (hT : ∀ a : Fin t → R, c.ε (T *ᵥ a) = r.ι (augmentation ∘ a)) :
    retractionMatrix c r * atOne T = 1 := by
  apply (evaluationEquiv t t).injective
  change evalMatrix (retractionMatrix c r * atOne T) = evalMatrix 1
  apply LinearMap.ext
  intro a
  rw [← evalMatrix_mulVec, retractionMatrix_eval]
  change r.p (c.ε (T *ᵥ a)) = (1 : Matrix (Fin t) (Fin t) (ZMod 2)) *ᵥ _
  rw [hT, one_mulVec]
  exact r.p_ι (show Trivial t from augmentation ∘ a)

/-- The corrected representative has zero first-layer component. -/
theorem correctedMatrix_p_zero
    (T : Matrix (Fin s) (Fin t) R) (V : Matrix (Fin s) (Fin n) R)
    (hT : ∀ a : Fin t → R, c.ε (T *ᵥ a) = r.ι (augmentation ∘ a))
    (w : Fin n → R) :
    r.p (c.ε (correctedMatrix T (retractionMatrix c r) V *ᵥ w)) = 0 := by
  rw [correctedMatrix_class c r T V hT, r.p_correction]

/-- The finite matrix equation `C V'(1)=0` holds for the corrected lift. -/
theorem correctedMatrix_atOne
    (T : Matrix (Fin s) (Fin t) R) (V : Matrix (Fin s) (Fin n) R)
    (hT : ∀ a : Fin t → R, c.ε (T *ᵥ a) = r.ι (augmentation ∘ a)) :
    retractionMatrix c r * atOne (correctedMatrix T (retractionMatrix c r) V) = 0 := by
  apply (evalMatrix_eq_zero_iff _).mp
  apply LinearMap.ext
  intro w
  rw [← evalMatrix_mulVec, retractionMatrix_eval]
  exact correctedMatrix_p_zero c r T V hT w

/-- Correction preserves `γV`, so a lift of `b₁` remains a lift after correction. -/
theorem correctedMatrix_γ (hπ : r.π = c.π)
    (T : Matrix (Fin s) (Fin t) R) (V : Matrix (Fin s) (Fin n) R)
    (hT : ∀ a : Fin t → R, c.ε (T *ᵥ a) = r.ι (augmentation ∘ a))
    (w : Fin n → R) :
    c.γ (correctedMatrix T (retractionMatrix c r) V *ᵥ w) = c.γ (V *ᵥ w) := by
  have h : c.π (c.ε (correctedMatrix T (retractionMatrix c r) V *ᵥ w)) =
      c.π (c.ε (V *ᵥ w)) := by
    rw [correctedMatrix_class c r T V hT, ← hπ, r.π_correction]
  exact congrArg c.j h

/-- The matrix formula descends to the constructed section of the actual syndrome sequence. -/
theorem correctedMatrix_descends (hπ : r.π = c.π)
    (T : Matrix (Fin s) (Fin t) R) (V : Matrix (Fin s) (Fin n) R)
    (hT : ∀ a : Fin t → R, c.ε (T *ᵥ a) = r.ι (augmentation ∘ a))
    (b₁ : (Fin n → R) →ₗ[R] c.L)
    (hV : ∀ w : Fin n → R, c.π (c.ε (V *ᵥ w)) = b₁ w)
    (w : Fin n → R) :
    r.σ (b₁ w) = c.ε (correctedMatrix T (retractionMatrix c r) V *ᵥ w) := by
  rw [correctedMatrix_class c r T V hT]
  have hw : r.π (c.ε (V *ᵥ w)) = b₁ w := by rw [hπ]; exact hV w
  rw [← hw, r.σ_π]

/-- Every column of `V'b₂` is an actual boundary. Only `b₁b₂=0` is needed
here; Koszul exactness supplies this condition for the manuscript's `b₂`. -/
theorem correctedMatrix_relations (hπ : r.π = c.π)
    (T : Matrix (Fin s) (Fin t) R) (V : Matrix (Fin s) (Fin n) R)
    (hT : ∀ a : Fin t → R, c.ε (T *ᵥ a) = r.ι (augmentation ∘ a))
    (b₁ : (Fin n → R) →ₗ[R] c.L)
    (hV : ∀ w : Fin n → R, c.π (c.ε (V *ᵥ w)) = b₁ w)
    (b₂ : Matrix (Fin n) (Fin m) R) (hrelations : b₁.comp b₂.mulVecLin = 0) :
    LinearMap.range (correctedMatrix T (retractionMatrix c r) V * b₂).mulVecLin ≤
      LinearMap.range c.d₁ := by
  rintro _ ⟨w, rfl⟩
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change c.ε ((correctedMatrix T (retractionMatrix c r) V * b₂) *ᵥ w) = 0
  rw [← Matrix.mulVec_mulVec,
    ← correctedMatrix_descends c r hπ T V hT b₁ hV]
  have hw : b₁ (b₂ *ᵥ w) = 0 := DFunLike.congr_fun hrelations w
  rw [hw, map_zero]

/-- Equation (C3), forward direction, for arbitrary Laurent representatives. -/
theorem β_representative_formula (hπ : r.π = c.π)
    (T : Matrix (Fin s) (Fin t) R) (V : Matrix (Fin s) (Fin n) R)
    (hT : ∀ a : Fin t → R, c.ε (T *ᵥ a) = r.ι (augmentation ∘ a))
    (b₁ : (Fin n → R) →ₗ[R] c.L)
    (hV : ∀ w : Fin n → R, c.π (c.ε (V *ᵥ w)) = b₁ w)
    (a : Fin t → R) (w : Fin n → R) :
    r.β (augmentation ∘ a, b₁ w) =
      c.ε (T *ᵥ a + correctedMatrix T (retractionMatrix c r) V *ᵥ w) := by
  change r.ι (augmentation ∘ a) + r.σ (b₁ w) = _
  calc
    r.ι (augmentation ∘ a) + r.σ (b₁ w) =
        c.ε (T *ᵥ a) + c.ε (correctedMatrix T (retractionMatrix c r) V *ᵥ w) :=
      congrArg₂ (· + ·) (hT a).symm
        (correctedMatrix_descends c r hπ T V hT b₁ hV w)
    _ = _ := (map_add c.ε _ _).symm

/-- Equation (C3), inverse direction: the coordinates are exactly `(Cv(1),γv)`. -/
theorem β_inverse_representative_formula (hπ : r.π = c.π) (v : Fin s → R) :
    r.β.symm (c.ε v) =
      (retractionMatrix c r *ᵥ (augmentation ∘ v), c.γ.rangeRestrict v) := by
  rw [r.β_symm_apply, hπ, c.π_mk]
  apply Prod.ext
  · exact (DFunLike.congr_fun (retractionMatrix_eval c r) v).symm
  · rfl

end Matrices

section StandardAugmentation

variable {q s k t₁ t₂ : ℕ}
variable (c : Syndrome.Cochain R (Fin q → R) (Fin s → R) (Fin k → R))

/-- The actual free-cover map after identifying the second cohomology layer
with the trivial module. -/
def trivialCover (e₂ : c.C2 ≃ₗ[R] Trivial t₂) :
    (Fin k → R) →ₗ[R] Trivial t₂ := e₂.toLinearMap.comp c.pQ

theorem trivialCover_surjective (e₂ : c.C2 ≃ₗ[R] Trivial t₂) :
    Function.Surjective (trivialCover c e₂) :=
  e₂.surjective.comp (LinearMap.range c.γ).mkQ_surjective

theorem range_eq_ker_trivialCover (e₂ : c.C2 ≃ₗ[R] Trivial t₂) :
    LinearMap.range c.γ = LinearMap.ker (trivialCover c e₂) := by
  ext v
  constructor
  · intro hv
    have hzero : c.pQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
    change e₂ (c.pQ v) = 0
    rw [hzero, map_zero]
  · intro hv
    have hzero : c.pQ v = 0 := e₂.injective (hv.trans (map_zero e₂).symm)
    exact (Submodule.Quotient.mk_eq_zero _).mp hzero

/-- The actual image `L` has the normalized form `R^h × J^t₂`, obtained by
applying the proved constant free-cover normalization to its quotient map. -/
def imageNormalization (e₂ : c.C2 ≃ₗ[R] Trivial t₂) :
    c.L ≃ₗ[R] ((Fin (k - t₂) → R) × (Fin t₂ → J)) :=
  (LinearEquiv.ofEq _ _ (range_eq_ker_trivialCover c e₂)).trans
    (Normalization.kernelEquiv (trivialCover c e₂) (trivialCover_surjective c e₂))

theorem second_layer_rank_le (e₂ : c.C2 ≃ₗ[R] Trivial t₂) : t₂ ≤ k :=
  Normalization.quotient_rank_le (trivialCover c e₂) (trivialCover_surjective c e₂)

/-- The standard augmentation isomorphism of Sections III.B and Appendix C.
Inputs are genuine layer identifications and a genuine retraction; neither
the desired section nor the free-cover normal form is assumed. -/
def augmentationIso (e₁ : Trivial t₁ ≃ₗ[R] c.C1) (e₂ : c.C2 ≃ₗ[R] Trivial t₂)
    (p : c.N →ₗ[R] Trivial t₁)
    (hp : p.comp (c.ι.comp e₁.toLinearMap) = LinearMap.id) :
    (Trivial t₁ × ((Fin (k - t₂) → R) × (Fin t₂ → J))) ≃ₗ[R] c.N :=
  ((LinearEquiv.refl R (Trivial t₁)).prodCongr (imageNormalization c e₂).symm).trans
    (ofSyndrome c e₁ p hp).β

/-- The inverse records the retraction coordinate and the normalized image of `γ`. -/
theorem augmentationIso_inverse_representative
    (e₁ : Trivial t₁ ≃ₗ[R] c.C1) (e₂ : c.C2 ≃ₗ[R] Trivial t₂)
    (p : c.N →ₗ[R] Trivial t₁)
    (hp : p.comp (c.ι.comp e₁.toLinearMap) = LinearMap.id) (v : Fin s → R) :
    (augmentationIso c e₁ e₂ p hp).symm (c.ε v) =
      (p (c.ε v), imageNormalization c e₂ (c.γ.rangeRestrict v)) := rfl

end StandardAugmentation

end

end Decoupling.ExplicitSplitting
