import Decoupling.HighDim.StableFreeLiftSystem

/-!
# Exact projective-lift systems for genuinely presented common targets

The common target of a Schanuel lifting square need not be projective.
It is represented by an injection into a module with a specified finite
presentation. Actual maps from projective retracts are represented by
finite matrices modulo those relations. This file proves both directions
between the finite scalar system and the genuine module lifting problem.
-/

namespace Decoupling.HighDim.StableFree.Effective

open Matrix CategoryTheory
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R]

/-- An actual target embeds faithfully in a supplied finitely presented
ambient module. It is not assumed projective or free. -/
structure PresentedTarget (M : ModuleCat.{u} R) where
  ambient : ModuleCat.{u} R
  size : ℕ
  relationCount : ℕ
  relationMatrix : Matrix (Fin size) (Fin relationCount) R
  project : Power R size →ₗ[R] ambient
  surjective : Function.Surjective project
  ker_project : LinearMap.ker project = LinearMap.range relationMatrix.mulVecLin
  embed : M →ₗ[R] ambient
  embed_injective : Function.Injective embed

namespace PresentedTarget
variable {M P Q : ModuleCat.{u} R}

/-- The original matrix presentation, with its actual quotient. -/
def ofPresentation {v h : ℕ} (D : Matrix (Fin v) (Fin h) R) :
    PresentedTarget (ModuleCat.of R (Power R v ⧸ LinearMap.range D.mulVecLin)) where
  ambient := ModuleCat.of R (Power R v ⧸ LinearMap.range D.mulVecLin)
  size := v
  relationCount := h
  relationMatrix := D
  project := (LinearMap.range D.mulVecLin).mkQ
  surjective := (LinearMap.range D.mulVecLin).mkQ_surjective
  ker_project := Submodule.ker_mkQ _
  embed := LinearMap.id
  embed_injective := Function.injective_id

/-- Actual syzygies embedded in known free terms use no relations. -/
def ofInjection (v : ℕ) (i : M →ₗ[R] Power R v) (hi : Function.Injective i) :
    PresentedTarget M where
  ambient := ModuleCat.of R (Power R v)
  size := v
  relationCount := 0
  relationMatrix := 0
  project := LinearMap.id
  surjective := Function.surjective_id
  ker_project := by simp
  embed := i
  embed_injective := hi

@[simp] theorem project_relation (t : PresentedTarget M) (w : Power R t.relationCount) :
    t.project (t.relationMatrix *ᵥ w) = 0 := by
  change t.relationMatrix.mulVecLin w ∈ LinearMap.ker t.project
  rw [t.ker_project]
  exact ⟨w,rfl⟩

/-- A finite matrix represents an actual map after passage through the
specified quotient. The module map itself is retained in the type. -/
structure Arrow (p : FiniteRetract P) (t : PresentedTarget M) (f : P →ₗ[R] M) where
  matrix : Matrix (Fin t.size) (Fin p.size) R
  equation : ∀ x, t.project (matrix *ᵥ x) = t.embed (f (p.project x))

/-- Turn an actual free-coordinate lift into its concrete representing matrix. -/
def Arrow.ofFreeLift (p : FiniteRetract P) (t : PresentedTarget M) (f : P →ₗ[R] M)
    (L : Power R p.size →ₗ[R] Power R t.size)
    (hL : t.project.comp L = t.embed.comp (f.comp p.project)) : Arrow p t f where
  matrix := LinearMap.toMatrix' L
  equation x := by
    rw [LinearMap.toMatrix'_mulVec]
    exact DFunLike.congr_fun hL x

/-- Existence of a representation uses only the free ambient domain. This
existence helper is not a costed representation algorithm. -/
theorem Arrow.exists (p : FiniteRetract P) (t : PresentedTarget M) (f : P →ₗ[R] M) :
    Nonempty (Arrow p t f) := by
  obtain ⟨L,hL⟩ := Module.projective_lifting_property t.project
    (t.embed.comp (f.comp p.project)) t.surjective
  exact ⟨Arrow.ofFreeLift p t f L hL⟩

section Lifting
variable (p : FiniteRetract P) (q : FiniteRetract Q) (t : PresentedTarget M)
  (f : P →ₗ[R] M) (g : Q →ₗ[R] M) (a : Arrow p t f) (b : Arrow q t g)

/-- Every solution of the actual relation equation gives a genuine module
lift. Projector constraints ensure its normalized finite representation. -/
theorem matrix_solution_lifts (X : Matrix (Fin p.size) (Fin q.size) R)
    (W : Matrix (Fin t.relationCount) (Fin q.size) R)
    (hX : a.matrix * X - b.matrix = t.relationMatrix * W) :
    f.comp (q.mapOfMatrix p X) = g := by
  apply LinearMap.ext
  intro x
  apply t.embed_injective
  have h := congrArg (fun L => t.project (L *ᵥ q.embed x)) hX
  rw [Matrix.sub_mulVec, map_sub, ← Matrix.mulVec_mulVec,
    a.equation, b.equation, q.project_embed,
    ← Matrix.mulVec_mulVec, t.project_relation] at h
  exact sub_eq_zero.mp h

/-- A genuine module lift gives normalized finite matrices solving all
three equations. Relation witnesses are chosen only for the finitely many
ordinary free columns, never from a basis of the projective module. -/
theorem matrices_of_lift (u : Q →ₗ[R] P) (hu : f.comp u = g) :
    ∃ X : Matrix (Fin p.size) (Fin q.size) R,
      ∃ W : Matrix (Fin t.relationCount) (Fin q.size) R,
        a.matrix*X-b.matrix=t.relationMatrix*W ∧
        p.projector*X=X ∧ X*q.projector=X := by
  classical
  let X := q.mapMatrix p u
  let V := a.matrix*X-b.matrix
  have hzero (x : Power R q.size) : t.project (V *ᵥ x) = 0 := by
    change t.project ((a.matrix*X-b.matrix) *ᵥ x) = 0
    rw [Matrix.sub_mulVec, map_sub, ← Matrix.mulVec_mulVec,
      a.equation, b.equation]
    change t.embed (f (p.project (q.mapMatrix p u *ᵥ x))) -
      t.embed (g (q.project x)) = 0
    rw [FiniteRetract.mapMatrix_mulVec, p.project_embed]
    have hh := DFunLike.congr_fun hu (q.project x)
    change f (u (q.project x)) = g (q.project x) at hh
    rw [hh, sub_self]
  have hcol (j : Fin q.size) : ∃ w : Power R t.relationCount,
      t.relationMatrix *ᵥ w = V.col j := by
    have hm : V.col j ∈ LinearMap.ker t.project := by
      have he : V *ᵥ Pi.single j 1 = V.col j := by
        funext i
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      have hz := hzero (Pi.single j 1)
      rwa [he] at hz
    rwa [t.ker_project] at hm
  choose w hw using hcol
  let W : Matrix (Fin t.relationCount) (Fin q.size) R := fun i j => w j i
  have hW : t.relationMatrix * W = V := by
    funext i j
    exact congrFun (hw j) i
  exact ⟨X,W,hW.symm,q.projector_mapMatrix p u,q.mapMatrix_projector p u⟩

/-- Exact scalar-system solvability is equivalent to the original module
lifting problem. No module is replaced by an arbitrary named certificate. -/
theorem lift_system_iff :
    (∃ z : LiftUnknowns p.size t.relationCount q.size → R,
      liftCoefficients a.matrix t.relationMatrix p.projector q.projector *ᵥ z =
        liftStack b.matrix 0 0) ↔ ∃ u : Q →ₗ[R] P, f.comp u = g := by
  rw [liftSolvable_iff]
  constructor
  · rintro ⟨X,W,hX,_,_⟩
    exact ⟨q.mapOfMatrix p X, matrix_solution_lifts p q t f g a b X W hX⟩
  · rintro ⟨u,hu⟩
    exact matrices_of_lift p q t f g a b u hu

/-- The exact finite system needed at every Schanuel stage is known
solvable by the actual surjection and the represented projective source. -/
theorem lift_system_solvable (hf : Function.Surjective f) :
    ∃ z : LiftUnknowns p.size t.relationCount q.size → R,
      liftCoefficients a.matrix t.relationMatrix p.projector q.projector *ᵥ z =
        liftStack b.matrix 0 0 := by
  let : Module.Projective R Q := q.projective
  exact (lift_system_iff p q t f g a b).mpr (Module.projective_lifting_property f g hf)

end Lifting
end PresentedTarget
end
end Decoupling.HighDim.StableFree.Effective
