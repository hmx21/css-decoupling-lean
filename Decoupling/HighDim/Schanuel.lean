import Decoupling.HighDim.StableCokernel
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Schanuel isomorphisms from actual projective lifts

HD012, `drafts/appendix.tex:958–965`.  The elementary Schanuel isomorphism
below is constructed from two lifts through the displayed surjections.
No freeness theorem for projective modules is used.  This is the local
step of the generalized Schanuel construction in `StableFreeResolution`.
-/

namespace Decoupling.HighDim.Schanuel

universe u
noncomputable section
variable {R : Type u} [Ring R]
variable {M A B : Type u} [AddCommGroup M] [AddCommGroup A] [AddCommGroup B]
  [Module R M] [Module R A] [Module R B]

/-- An explicit Schanuel map from lifts `u` and `v`. -/
def equivOfLifts (f : A →ₗ[R] M) (g : B →ₗ[R] M)
    (u : B →ₗ[R] A) (v : A →ₗ[R] B)
    (hu : f.comp u = g) (hv : g.comp v = f) :
    (LinearMap.ker f × B) ≃ₗ[R] (LinearMap.ker g × A) where
  toFun x := (⟨v ((x.1 : A) + u x.2) - x.2, by
    change g (v ((x.1 : A) + u x.2) - x.2) = 0
    have hv' := DFunLike.congr_fun hv ((x.1 : A) + u x.2)
    have hu' := DFunLike.congr_fun hu x.2
    change g (v _) = f _ at hv'
    change f (u _) = g _ at hu'
    rw [map_sub, hv', map_add, x.1.property, hu', zero_add, sub_self]⟩,
      (x.1 : A) + u x.2)
  invFun y := (⟨y.2 - u (v y.2 - (y.1 : B)), by
    change f (y.2 - u (v y.2 - (y.1 : B))) = 0
    have hu' := DFunLike.congr_fun hu (v y.2 - (y.1 : B))
    have hv' := DFunLike.congr_fun hv y.2
    change f (u _) = g _ at hu'
    change g (v _) = f _ at hv'
    rw [map_sub, hu', map_sub, hv', y.1.property, sub_zero, sub_self]⟩,
      v y.2 - (y.1 : B))
  left_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [sub_sub_cancel]
      abel
    · simp
  right_inv y := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [sub_add_cancel]
      abel
    · simp
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]
      abel
    · simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]
      abel
  map_smul' r x := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_add, map_smul,
        smul_add, smul_sub, RingHom.id_apply]
    · simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul,
        smul_add, RingHom.id_apply]

/-- The only choices are solutions of the two solvable linear lifting equations. -/
def equiv (f : A →ₗ[R] M) (g : B →ₗ[R] M)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    [Module.Projective R A] [Module.Projective R B] :
    (LinearMap.ker f × B) ≃ₗ[R] (LinearMap.ker g × A) :=
  equivOfLifts f g
    (Module.projective_lifting_property f g hf).choose
    (Module.projective_lifting_property g f hg).choose
    (Module.projective_lifting_property f g hf).choose_spec
    (Module.projective_lifting_property g f hg).choose_spec

/-- Transporting the codomain through an actual isomorphism preserves the
actual kernel, with its elementwise inclusion unchanged. -/
def kerPostcompEquiv {N : Type u} [AddCommGroup N] [Module R N]
    (f : A →ₗ[R] M) (e : M ≃ₗ[R] N) :
    LinearMap.ker (e.toLinearMap.comp f) ≃ₗ[R] LinearMap.ker f :=
  LinearEquiv.ofEq _ _ (by
    ext x
    change e (f x) = 0 ↔ f x = 0
    exact e.map_eq_zero_iff)

/-- Adding a projective direct summand to a presentation leaves its kernel
unchanged. This equivalence requires no basis of that summand. -/
def kerProdEquiv {P : Type u} [AddCommGroup P] [Module R P]
    (f : A →ₗ[R] M) :
    LinearMap.ker (f.prodMap (LinearMap.id : P →ₗ[R] P)) ≃ₗ[R] LinearMap.ker f where
  toFun x := ⟨x.val.1, congrArg Prod.fst x.property⟩
  invFun x := ⟨(x.val, 0), by exact Prod.ext x.property (by simp)⟩
  left_inv x := by
    apply Subtype.ext
    change (x.val.1, 0) = x.val
    apply Prod.ext
    · rfl
    · exact (congrArg Prod.snd x.property).symm
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' r x := rfl

end
end Decoupling.HighDim.Schanuel
