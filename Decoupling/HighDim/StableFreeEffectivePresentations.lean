import Decoupling.HighDim.StableFreeStageRepresentation

/-!
# Presentations and retracts constructed from the actual Schanuel data

The initial targets and every actual syzygy receive finite presentations
from the supplied finite free resolution maps. Products with projective
retracts retain explicit ambient ranks and relations. The complement is
represented by its previously proved concrete retraction, never a free basis.
-/

namespace Decoupling.HighDim.StableFree.Effective

open Matrix CategoryTheory
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R]

namespace PresentedTarget
variable {M P F F₁ : ModuleCat.{u} R}

/-- Adjoin a known finite projective retract to an actual presented target.
The relation count is unchanged; only the ambient free rank is enlarged. -/
def prod (t : PresentedTarget M) (p : FiniteRetract P) :
    PresentedTarget (ModuleCat.of R (M × P)) := by
  let e := powerAdd (R := R) t.size p.size
  let L : Power R t.relationCount →ₗ[R] Power R (t.size+p.size) :=
    e.toLinearMap.comp ((LinearMap.inl R (Power R t.size) (Power R p.size)).comp
      t.relationMatrix.mulVecLin)
  refine {
    ambient := ModuleCat.of R (t.ambient × Power R p.size)
    size := t.size+p.size
    relationCount := t.relationCount
    relationMatrix := LinearMap.toMatrix' L
    project := (t.project.prodMap LinearMap.id).comp e.symm.toLinearMap
    surjective := ?_
    ker_project := ?_
    embed := t.embed.prodMap p.embed
    embed_injective := ?_ }
  · rintro ⟨x,y⟩
    obtain ⟨a,ha⟩ := t.surjective x
    refine ⟨e (a,y),?_⟩
    change (t.project (e.symm (e (a,y))).1,(e.symm (e (a,y))).2) = (x,y)
    rw [e.symm_apply_apply,ha]
  · ext x
    change (t.project (e.symm x).1,(e.symm x).2) = 0 ↔
      ∃ w, LinearMap.toMatrix' L *ᵥ w = x
    constructor
    · intro hx
      have h₁ : (e.symm x).1 ∈ LinearMap.ker t.project := congrArg Prod.fst hx
      have h₂ : (e.symm x).2 = 0 := congrArg Prod.snd hx
      rw [t.ker_project] at h₁
      obtain ⟨w,hw⟩ := h₁
      refine ⟨w,?_⟩
      rw [LinearMap.toMatrix'_mulVec]
      change e (t.relationMatrix *ᵥ w,0) = x
      apply e.symm.injective
      rw [e.symm_apply_apply]
      exact Prod.ext hw h₂.symm
    · rintro ⟨w,rfl⟩
      rw [LinearMap.toMatrix'_mulVec]
      change (t.project (e.symm (e (t.relationMatrix *ᵥ w,0))).1,
        (e.symm (e (t.relationMatrix *ᵥ w,0))).2) = 0
      rw [e.symm_apply_apply,t.project_relation]
      rfl
  · intro x y h
    apply Prod.ext
    · exact t.embed_injective (congrArg Prod.fst h)
    · exact p.embed_injective (congrArg Prod.snd h)

/-- Two consecutive genuine free covers yield the displayed finite
presentation, with no choice of generators for the syzygy. -/
def ofCover (v w : ℕ) (c : F ≃ₗ[R] Power R v) (c₁ : F₁ ≃ₗ[R] Power R w)
    (π : F →ₗ[R] M) (hπ : Function.Surjective π)
    (ι : F₁ →ₗ[R] LinearMap.ker π) (hι : Function.Surjective ι) : PresentedTarget M := by
  let L := c.toLinearMap.comp ((LinearMap.ker π).subtype.comp (ι.comp c₁.symm.toLinearMap))
  refine {
    ambient := M
    size := v
    relationCount := w
    relationMatrix := LinearMap.toMatrix' L
    project := π.comp c.symm.toLinearMap
    surjective := hπ.comp c.symm.surjective
    ker_project := ?_
    embed := LinearMap.id
    embed_injective := Function.injective_id }
  ext x
  change π (c.symm x) = 0 ↔ ∃ y, LinearMap.toMatrix' L *ᵥ y = x
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := hι ⟨c.symm x,hx⟩
    refine ⟨c₁ y,?_⟩
    rw [LinearMap.toMatrix'_mulVec]
    change c (ι (c₁.symm (c₁ y))).val = x
    rw [c₁.symm_apply_apply,hy,c.apply_symm_apply]
  · rintro ⟨y,hy⟩
    rw [←hy,LinearMap.toMatrix'_mulVec]
    change π (c.symm (c (ι (c₁.symm y)).val)) = 0
    rw [c.symm_apply_apply]
    exact (ι (c₁.symm y)).property

/-- Every input resolution gives its own actual target presentation. The
first two known free ranks are used; the length-zero cases use empty blocks. -/
def ofResolution : {n : ℕ} → {M : ModuleCat.{u} R} → Resolution R n M → PresentedTarget M
  | 0, M, .zero e => {
      ambient := M
      size := 0
      relationCount := 0
      relationMatrix := 0
      project := e.symm.toLinearMap
      surjective := e.symm.surjective
      ker_project := Subsingleton.elim _ _
      embed := LinearMap.id
      embed_injective := Function.injective_id }
  | _+1, _, .step F v c π hπ tail => by
      cases tail with
      | zero e =>
          letI : Subsingleton (LinearMap.ker π) := e.injective.subsingleton
          exact ofCover (F₁ := ModuleCat.of R (Power R 0)) v 0 c
            (LinearEquiv.refl R _) π hπ 0 (fun x => ⟨0,Subsingleton.elim _ _⟩)
      | step F₁ w c₁ ι hι tail =>
          exact ofCover v w c c₁ π hπ ι hι

end PresentedTarget

/-- The actual C4 kernel has the explicit finite-free retract supplied by
its error-factorization maps, with ambient rank equal to the two error ranks. -/
def complementRetract {M N P Q : ModuleCat.{u} R}
    (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (ξM : M →ₗ[R] P) (ζM : P →ₗ[R] M)
    (ξN : N →ₗ[R] Q) (ζN : Q →ₗ[R] N)
    (hM : LinearMap.id - g.comp f = ζM.comp ξM)
    (hN : LinearMap.id - f.comp g = ζN.comp ξN)
    (p : FiniteRetract P) (q : FiniteRetract Q) :
    FiniteRetract (ModuleCat.of R (StableCokernel.Complement g ζM)) :=
  (q.prod p).ofRetraction (StableCokernel.complementEmbedding g ζM ξN)
    (StableCokernel.complementRetraction f g ξM ζM ζN hM)
    (StableCokernel.complement_retract f g ξM ζM ξN ζN hM hN)

end
end Decoupling.HighDim.StableFree.Effective
