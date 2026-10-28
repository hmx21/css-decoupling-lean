import Decoupling.HighDim.StableFreeEffectiveStep
import Decoupling.HighDim.StableFreeEffectivePresentations

/-!
# Known arrows at every embedded syzygy stage

The left cover uses its given differential and the old projector. The right
cover is its corresponding block matrix followed by the already computed
inverse equivalence. These are explicit representations; no representation
lift is selected. The common target has zero relations because it is embedded
in a known free module.
-/

namespace Decoupling.HighDim.StableFree.Effective
open Matrix CategoryTheory
universe u
noncomputable section
variable {R : Type u} [CommRing R]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Diagonal blocks in the fixed finite-coordinate enumeration. -/
def diagonalBlocks {a b c d : ℕ} (A : Matrix (Fin a) (Fin c) R)
    (B : Matrix (Fin b) (Fin d) R) : Matrix (Fin (a+b)) (Fin (c+d)) R :=
  rowBlocks (columnBlocks A 0) (columnBlocks 0 B)

theorem diagonalBlocks_mulVec {a b c d : ℕ} (A : Matrix (Fin a) (Fin c) R)
    (B : Matrix (Fin b) (Fin d) R) (x : Power R c) (y : Power R d) :
    diagonalBlocks A B *ᵥ powerAdd c d (x,y) = powerAdd a b (A *ᵥ x,B *ᵥ y) := by
  rw [diagonalBlocks,rowBlocks_mulVec,columnBlocks_mulVec,columnBlocks_mulVec]
  simp only [Matrix.zero_mulVec,zero_add,add_zero]

variable {M N P Q F G : ModuleCat.{u} R}

theorem free_prod_projector (a : ℕ) (c : F ≃ₗ[R] Power R a) (p : FiniteRetract P) :
    ((FiniteRetract.ofCoordinates a c).prod p).projector =
      diagonalBlocks (1 : Matrix (Fin a) (Fin a) R) p.projector := by
  apply Matrix.ext_of_mulVec_single
  intro j
  generalize (Pi.single j 1 : Power R (a+p.size)) = x
  obtain ⟨⟨x,y⟩,rfl⟩ := (powerAdd (R := R) a p.size).surjective x
  rw [diagonalBlocks_mulVec,FiniteRetract.projector_mulVec,Matrix.one_mulVec,
    FiniteRetract.projector_mulVec]
  change powerAdd a p.size
    (c (c.symm ((powerAdd a p.size).symm (powerAdd a p.size (x,y))).1),
      p.embed (p.project ((powerAdd a p.size).symm (powerAdd a p.size (x,y))).2)) = _
  rw [LinearEquiv.symm_apply_apply,c.apply_symm_apply]

/-- The actual common target for an embedded stage. -/
def embeddedTarget (m : FiniteEmbedding M) (p : FiniteRetract P) :
    PresentedTarget (ModuleCat.of R (M × P)) :=
  (PresentedTarget.ofInjection m.size m.embed m.injective).prod p

@[simp] theorem embeddedTarget_size (m : FiniteEmbedding M) (p : FiniteRetract P) :
    (embeddedTarget m p).size = m.size+p.size := rfl
@[simp] theorem embeddedTarget_relationCount (m : FiniteEmbedding M) (p : FiniteRetract P) :
    (embeddedTarget m p).relationCount = 0 := rfl
@[simp] theorem free_prod_size (a : ℕ) (c : F ≃ₗ[R] Power R a) (p : FiniteRetract P) :
    ((FiniteRetract.ofCoordinates a c).prod p).size = a+p.size := rfl

@[simp] theorem embeddedTarget_relations (m : FiniteEmbedding M) (p : FiniteRetract P) :
    (embeddedTarget m p).relationMatrix = 0 := by
  funext i j
  exact Fin.elim0 j

/-- Given free-cover coordinates, this is its literal ambient matrix. -/
def coverMatrix (m : FiniteEmbedding M) (a : ℕ) (c : F ≃ₗ[R] Power R a)
    (f : F →ₗ[R] M) : Matrix (Fin m.size) (Fin a) R :=
  LinearMap.toMatrix' (m.embed.comp (f.comp c.symm.toLinearMap))

@[simp] theorem coverMatrix_mulVec (m : FiniteEmbedding M) (a : ℕ)
    (c : F ≃ₗ[R] Power R a) (f : F →ₗ[R] M) (x : Power R a) :
    coverMatrix m a c f *ᵥ x = m.embed (f (c.symm x)) :=
  LinearMap.toMatrix'_mulVec _ _

/-- Explicit left arrow, built directly from the supplied differential. -/
def embeddedLeftArrow (m : FiniteEmbedding M) (p : FiniteRetract P)
    (a : ℕ) (c : F ≃ₗ[R] Power R a) (f : F →ₗ[R] M) :
    PresentedTarget.Arrow ((FiniteRetract.ofCoordinates a c).prod p)
      (embeddedTarget m p) (stageLeft f) where
  matrix := diagonalBlocks (coverMatrix m a c f) p.projector
  equation := by
    intro x
    obtain ⟨⟨x,y⟩,rfl⟩ := (powerAdd (R := R) a p.size).surjective x
    change (powerAdd m.size p.size).symm
      (diagonalBlocks (coverMatrix m a c f) p.projector *ᵥ powerAdd a p.size (x,y)) =
      (m.embed (f (c.symm ((powerAdd a p.size).symm (powerAdd a p.size (x,y))).1)),
        p.embed (p.project ((powerAdd a p.size).symm (powerAdd a p.size (x,y))).2))
    rw [diagonalBlocks_mulVec,coverMatrix_mulVec,FiniteRetract.projector_mulVec,
      LinearEquiv.symm_apply_apply]
    rw [LinearEquiv.symm_apply_apply]


/-- Explicit right arrow, composed with the inverse matrix already stored
in the state. -/
def embeddedRightArrow (m : FiniteEmbedding M) (n : FiniteEmbedding N)
    (p : FiniteRetract P) (q : FiniteRetract Q) (e : EmbeddedEquiv m n p q)
    (b : ℕ) (c : G ≃ₗ[R] Power R b) (g : G →ₗ[R] N) :
    PresentedTarget.Arrow ((FiniteRetract.ofCoordinates b c).prod q)
      (embeddedTarget m p) (stageRight g e.equiv) where
  matrix := e.inverse * diagonalBlocks (coverMatrix n b c g) q.projector
  equation := by
    intro x
    obtain ⟨⟨x,y⟩,rfl⟩ := (powerAdd (R := R) b q.size).surjective x
    rw [←Matrix.mulVec_mulVec,diagonalBlocks_mulVec,coverMatrix_mulVec,
      FiniteRetract.projector_mulVec]
    have h := e.inverse_eq (g (c.symm x),q.project y)
    change e.inverse *ᵥ powerAdd n.size q.size
      (n.embed (g (c.symm x)),q.embed (q.project y)) =
      powerAdd m.size p.size
        (m.embed (e.equiv.symm (g (c.symm x),q.project y)).1,
         p.embed (e.equiv.symm (g (c.symm x),q.project y)).2) at h
    rw [h]
    change (powerAdd m.size p.size).symm
      (powerAdd m.size p.size
        (m.embed (e.equiv.symm (g (c.symm x),q.project y)).1,
          p.embed (e.equiv.symm (g (c.symm x),q.project y)).2)) =
      (m.embed (e.equiv.symm
        (g (c.symm ((powerAdd b q.size).symm (powerAdd b q.size (x,y))).1),
          q.project ((powerAdd b q.size).symm (powerAdd b q.size (x,y))).2)).1,
       p.embed (e.equiv.symm
        (g (c.symm ((powerAdd b q.size).symm (powerAdd b q.size (x,y))).1),
          q.project ((powerAdd b q.size).symm (powerAdd b q.size (x,y))).2)).2)
    simp only [LinearEquiv.symm_apply_apply]

theorem stageLeft_surjective (f : F →ₗ[R] M) (hf : Function.Surjective f) :
    Function.Surjective (stageLeft (P := P) f) := by
  rintro ⟨m,p⟩
  obtain ⟨x,rfl⟩ := hf m
  exact ⟨(x,p),rfl⟩

theorem stageRight_surjective (g : G →ₗ[R] N) (hg : Function.Surjective g)
    (e : (M × P) ≃ₗ[R] (N × Q)) : Function.Surjective (stageRight g e) := by
  intro x
  obtain ⟨y,hy⟩ := hg (e x).1
  refine ⟨(y,(e x).2),?_⟩
  change e.symm (g y,(e x).2) = x
  rw [hy,Prod.eta,e.symm_apply_apply]

end
end Decoupling.HighDim.StableFree.Effective
