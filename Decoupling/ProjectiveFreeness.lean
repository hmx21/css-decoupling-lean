import Decoupling.IdempotentPresentation

/-!
# Exact matrix criteria and transport of native projective freeness

The criterion below is equivalent to native freeness of all finite projective
modules; it is not a replacement definition for `Module.Free`.
-/

namespace Decoupling.ProjectiveFreeness

open IdempotentPresentation

noncomputable section

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- Every actual idempotent image is a native free module. -/
def IdempotentCriterion (A : Type u) [CommRing A] : Prop :=
  ∀ (n : ℕ) (E : Matrix (Fin n) (Fin n) A), E * E = E →
    Module.Free A (LinearMap.range E.mulVecLin)

theorem criterion_iff_native : IdempotentCriterion A ↔
    ∀ (P : Type u) [AddCommGroup P] [Module A P]
      [Module.Finite A P] [Module.Projective A P], Module.Free A P := by
  constructor
  · intro h P _ _ _ _
    obtain ⟨n, E, hE, ⟨e⟩⟩ := exists_idempotent (A := A) (P := P)
    have := h n E hE
    exact Module.Free.of_equiv e.symm
  · intro h n E hE
    have := projective_range E hE
    exact h (LinearMap.range E.mulVecLin)

/-- A free image remains free after any ring map, by mapping its rectangular
inverse factors. No flatness hypothesis is needed for this idempotent image. -/
theorem free_range_map [Nontrivial A] {n : ℕ}
    (E : Matrix (Fin n) (Fin n) A) (hE : E * E = E)
    (hf : Module.Free A (LinearMap.range E.mulVecLin)) (f : A →+* B) :
    Module.Free B (LinearMap.range (E.map f).mulVecLin) := by
  obtain ⟨k, F, G, hFG, hGF⟩ := (free_iff_factorization E hE).mp hf
  exact free_of_factorization (E.map f) (by rw [← Matrix.map_mul, hE])
    (F.map f) (G.map f) (by rw [← Matrix.map_mul, hFG])
    (by rw [← Matrix.map_mul, hGF, Matrix.map_one _ (map_zero _) (map_one _)])

/-- A ring equivalence transports the exact native-freeness criterion. -/
theorem criterion_of_ringEquiv [Nontrivial A] (e : A ≃+* B)
    (h : IdempotentCriterion A) : IdempotentCriterion B := by
  intro n E hE
  let E' := E.map e.symm
  have hE' : E' * E' = E' := by
    dsimp only [E']
    rw [← Matrix.map_mul, hE]
  have hf := free_range_map E' hE' (h n E' hE') e.toRingHom
  have he : E'.map e.toRingHom = E := by
    funext i j
    exact e.apply_symm_apply (E i j)
  rwa [he] at hf

end
end Decoupling.ProjectiveFreeness
