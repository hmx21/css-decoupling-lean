import Decoupling.HighDim.Schanuel
import Mathlib.LinearAlgebra.Pi

/-!
# Generalized Schanuel with explicit free ranks

HD012, `drafts/appendix.tex:958–965`.  A resolution here consists of actual
surjections from specified finite powers of the ring, followed recursively
by resolutions of their actual kernels.  Hence exactness is built into the
maps, not replaced by an assumed stable isomorphism.  The generalized
Schanuel equivalence uses only projective lifts through these surjections.
-/

namespace Decoupling.HighDim.StableFree

universe u
noncomputable section
variable (R : Type u) [Ring R]

abbrev Power (n : ℕ) := Fin n → R

/-- Finite free resolution with prescribed free coordinates at every term.
Length zero means that the augmented module itself is zero. -/
inductive Resolution : ℕ → ModuleCat.{u} R → Type (u + 1)
  | zero {M : ModuleCat.{u} R} (e : M ≃ₗ[R] Power R 0) : Resolution 0 M
  | step {n : ℕ} {M : ModuleCat.{u} R} (F : ModuleCat.{u} R) (rank : ℕ)
      (coordinates : F ≃ₗ[R] Power R rank) (π : F →ₗ[R] M) (surj : Function.Surjective π)
      (tail : Resolution n (ModuleCat.of R (LinearMap.ker π))) : Resolution (n + 1) M

variable {R}

/-- The explicit concatenation of two finite coordinate blocks. -/
def powerAdd (a b : ℕ) : (Power R a × Power R b) ≃ₗ[R] Power R (a + b) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) R R).symm.trans
    (LinearEquiv.funCongrLeft R R (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).symm)

/-- Discarding a genuinely zero module is an explicit linear isomorphism. -/
def zeroLeft (M P : ModuleCat.{u} R) (e : M ≃ₗ[R] Power R 0) : (M × P) ≃ₗ[R] P where
  toFun := Prod.snd
  invFun x := (0, x)
  left_inv x := by
    apply Prod.ext
    · apply e.injective
      exact Subsingleton.elim _ _
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Empty stabilization adds no coordinates. -/
def powerZeroRight (P : ModuleCat.{u} R) : (P × Power R 0) ≃ₗ[R] P :=
  (LinearEquiv.prodComm R P (Power R 0)).trans
    (zeroLeft (ModuleCat.of R (Power R 0)) P (LinearEquiv.refl _ _))

/-- Reordering and concatenating known free blocks, without a basis choice. -/
def collectRight (P : ModuleCat.{u} R) (a b : ℕ) :
    ((Power R a × P) × Power R b) ≃ₗ[R] (P × Power R (a + b)) :=
  ((LinearEquiv.prodComm R (Power R a) P).prodCongr (LinearEquiv.refl _ _)).trans
    ((LinearEquiv.prodAssoc R P (Power R a) (Power R b)).trans
      ((LinearEquiv.refl R P).prodCongr (powerAdd a b)))

namespace Resolution

/-- The two alternating rank totals.  For successive terms they obey
`A = rank(F₀) + B_tail`, `B = rank(G₀) + A_tail`. -/
def ranks : {n : ℕ} → {M N : ModuleCat.{u} R} →
    Resolution R n M → Resolution R n N → ℕ × ℕ
  | 0, _, _, .zero _, .zero _ => (0, 0)
  | _ + 1, _, _, .step _ r _ _ _ F, .step _ s _ _ _ G =>
      (r + (ranks F G).2, s + (ranks F G).1)

/-- Generalized Schanuel, with exactly the alternating ranks of the supplied
finite free resolutions.  `P` and `Q` need only be projective, never free. -/
def stabilize : {n : ℕ} → {M N : ModuleCat.{u} R} →
    (F : Resolution R n M) → (G : Resolution R n N) →
    (P Q : ModuleCat.{u} R) → [Module.Projective R P] → [Module.Projective R Q] →
    ((M × P) ≃ₗ[R] (N × Q)) →
    (P × Power R (ranks F G).1) ≃ₗ[R] (Q × Power R (ranks F G).2)
  | 0, M, N, .zero eM, .zero eN, P, Q, _, _, e =>
      (powerZeroRight P).trans
        ((zeroLeft M P eM).symm.trans
          (e.trans ((zeroLeft N Q eN).trans (powerZeroRight Q).symm)))
  | n + 1, _, _, .step F₀ r cF f hf F, .step G₀ s cG g hg G, P, Q, _, _, e => by
      letI : Module.Free R F₀ := Module.Free.of_equiv cF.symm
      letI : Module.Free R G₀ := Module.Free.of_equiv cG.symm
      let f' := f.prodMap (LinearMap.id : P →ₗ[R] P)
      let g' := e.symm.toLinearMap.comp (g.prodMap (LinearMap.id : Q →ₗ[R] Q))
      have hf' : Function.Surjective f' := by
        rintro ⟨m,p⟩
        obtain ⟨a, rfl⟩ := hf m
        exact ⟨(a,p), rfl⟩
      have hg' : Function.Surjective g' := by
        intro x
        obtain ⟨a, ha⟩ := hg (e x).1
        exact ⟨(a,(e x).2), by change e.symm (g a, (e x).2) = x; rw [ha]; simp⟩
      let kf : LinearMap.ker f' ≃ₗ[R] LinearMap.ker f := Schanuel.kerProdEquiv f
      let kg : LinearMap.ker g' ≃ₗ[R] LinearMap.ker g :=
        (Schanuel.kerPostcompEquiv _ e.symm).trans (Schanuel.kerProdEquiv g)
      let e' : (LinearMap.ker f × (G₀ × Q)) ≃ₗ[R]
          (LinearMap.ker g × (F₀ × P)) :=
        (kf.symm.prodCongr (LinearEquiv.refl _ _)).trans
          ((Schanuel.equiv f' g' hf' hg').trans
            (kg.prodCongr (LinearEquiv.refl _ _)))
      let ih := stabilize F G (ModuleCat.of R (G₀ × Q))
        (ModuleCat.of R (F₀ × P)) e'
      let cP := ((cF.prodCongr (LinearEquiv.refl R P)).prodCongr
        (LinearEquiv.refl R (Power R (ranks F G).2))).trans
          (collectRight P r (ranks F G).2)
      let cQ := ((cG.prodCongr (LinearEquiv.refl R Q)).prodCongr
        (LinearEquiv.refl R (Power R (ranks F G).1))).trans
          (collectRight Q s (ranks F G).1)
      exact cP.symm.trans (ih.symm.trans cQ)

end Resolution
end
end Decoupling.HighDim.StableFree
