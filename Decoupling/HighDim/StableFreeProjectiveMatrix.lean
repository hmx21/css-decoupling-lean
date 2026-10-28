import Decoupling.HighDim.StableFreeResolution
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite matrix representations of actual projective retracts

HD012 effective Schanuel implementation. The projective module is retained
as the actual module equipped with its explicit finite-free embedding and
retraction. No basis of that module is introduced. Its projector and every
map are actual finite matrices, with the normalization equations proved.
-/

namespace Decoupling.HighDim.StableFree.Effective

open Matrix CategoryTheory
universe u
noncomputable section
variable {R : Type u} [CommRing R]

/-- Explicit representation of a module as a retract of a known finite free
module. This is supplied constructively for the C4 kernel, not assumed free. -/
structure FiniteRetract (P : ModuleCat.{u} R) where
  size : ℕ
  embed : P →ₗ[R] Power R size
  project : Power R size →ₗ[R] P
  retract : project.comp embed = LinearMap.id

namespace FiniteRetract
variable {P Q T : ModuleCat.{u} R}

@[simp] theorem project_embed (p : FiniteRetract P) (x : P) : p.project (p.embed x) = x :=
  DFunLike.congr_fun p.retract x

theorem embed_injective (p : FiniteRetract P) : Function.Injective p.embed :=
  Function.LeftInverse.injective p.project_embed

theorem projective (p : FiniteRetract P) : Module.Projective R P :=
  Module.Projective.of_split p.embed p.project p.retract

theorem finite (p : FiniteRetract P) : Module.Finite R P :=
  Module.Finite.of_surjective p.project (fun x => ⟨p.embed x,p.project_embed x⟩)

/-- A supplied free-coordinate block has its tautological finite retract. -/
def ofCoordinates (n : ℕ) (e : P ≃ₗ[R] Power R n) : FiniteRetract P where
  size := n
  embed := e.toLinearMap
  project := e.symm.toLinearMap
  retract := by ext x; exact e.symm_apply_apply x

/-- A further actual retract inherits finite coordinates without selecting a basis. -/
def ofRetraction (q : FiniteRetract Q) (i : P →ₗ[R] Q) (s : Q →ₗ[R] P)
    (h : s.comp i = LinearMap.id) : FiniteRetract P where
  size := q.size
  embed := q.embed.comp i
  project := s.comp q.project
  retract := by
    ext x
    change s (q.project (q.embed (i x))) = x
    rw [q.project_embed]
    exact DFunLike.congr_fun h x

/-- Direct sum of actual finite retracts, with exactly the sum of ambient ranks. -/
def prod (p : FiniteRetract P) (q : FiniteRetract Q) :
    FiniteRetract (ModuleCat.of R (P × Q)) where
  size := p.size + q.size
  embed := (powerAdd p.size q.size).toLinearMap.comp (p.embed.prodMap q.embed)
  project := (p.project.prodMap q.project).comp (powerAdd p.size q.size).symm.toLinearMap
  retract := by
    apply LinearMap.ext
    intro x
    change (p.project ((powerAdd p.size q.size).symm
      (powerAdd p.size q.size (p.embed x.1,q.embed x.2))).1,
      q.project ((powerAdd p.size q.size).symm
      (powerAdd p.size q.size (p.embed x.1,q.embed x.2))).2) = x
    rw [LinearEquiv.symm_apply_apply]
    exact Prod.ext (p.project_embed x.1) (q.project_embed x.2)

/-- The actual idempotent in the known free coordinates. -/
def projector (p : FiniteRetract P) : Matrix (Fin p.size) (Fin p.size) R :=
  LinearMap.toMatrix' (p.embed.comp p.project)

@[simp] theorem projector_mulVec (p : FiniteRetract P) (x : Power R p.size) :
    p.projector *ᵥ x = p.embed (p.project x) :=
  LinearMap.toMatrix'_mulVec _ _

theorem projector_idempotent (p : FiniteRetract P) : p.projector * p.projector = p.projector := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec, projector_mulVec, projector_mulVec,
    project_embed]

/-- Every actual linear map is represented by its normalized ambient matrix. -/
def mapMatrix (p : FiniteRetract P) (q : FiniteRetract Q) (f : P →ₗ[R] Q) :
    Matrix (Fin q.size) (Fin p.size) R :=
  LinearMap.toMatrix' (q.embed.comp (f.comp p.project))

@[simp] theorem mapMatrix_mulVec (p : FiniteRetract P) (q : FiniteRetract Q)
    (f : P →ₗ[R] Q) (x : Power R p.size) :
    p.mapMatrix q f *ᵥ x = q.embed (f (p.project x)) :=
  LinearMap.toMatrix'_mulVec _ _

theorem projector_mapMatrix (p : FiniteRetract P) (q : FiniteRetract Q) (f : P →ₗ[R] Q) :
    q.projector * p.mapMatrix q f = p.mapMatrix q f := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec, mapMatrix_mulVec, projector_mulVec,
    project_embed]

theorem mapMatrix_projector (p : FiniteRetract P) (q : FiniteRetract Q) (f : P →ₗ[R] Q) :
    p.mapMatrix q f * p.projector = p.mapMatrix q f := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec, projector_mulVec, mapMatrix_mulVec,
    project_embed, mapMatrix_mulVec]

/-- A matrix acts between the represented modules by embedding and projecting. -/
def mapOfMatrix (p : FiniteRetract P) (q : FiniteRetract Q)
    (X : Matrix (Fin q.size) (Fin p.size) R) : P →ₗ[R] Q :=
  q.project.comp (X.mulVecLin.comp p.embed)

@[simp] theorem mapOfMatrix_apply (p : FiniteRetract P) (q : FiniteRetract Q)
    (X : Matrix (Fin q.size) (Fin p.size) R) (x : P) :
    p.mapOfMatrix q X x = q.project (X *ᵥ p.embed x) := rfl

@[simp] theorem mapOfMatrix_mapMatrix (p : FiniteRetract P) (q : FiniteRetract Q)
    (f : P →ₗ[R] Q) : p.mapOfMatrix q (p.mapMatrix q f) = f := by
  ext x
  rw [mapOfMatrix_apply, mapMatrix_mulVec, project_embed, project_embed]

/-- Matrix reconstruction is exactly the two projector normalizations. -/
theorem mapMatrix_mapOfMatrix (p : FiniteRetract P) (q : FiniteRetract Q)
    (X : Matrix (Fin q.size) (Fin p.size) R) :
    p.mapMatrix q (p.mapOfMatrix q X) = q.projector * X * p.projector := by
  apply Matrix.mulVec_injective
  funext x
  rw [mapMatrix_mulVec, mapOfMatrix_apply,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, projector_mulVec, projector_mulVec]

/-- Source and target projector equations suffice for exact matrix recovery. -/
theorem mapMatrix_mapOfMatrix_of_normalized (p : FiniteRetract P) (q : FiniteRetract Q)
    (X : Matrix (Fin q.size) (Fin p.size) R)
    (hleft : q.projector * X = X) (hright : X * p.projector = X) :
    p.mapMatrix q (p.mapOfMatrix q X) = X := by
  rw [mapMatrix_mapOfMatrix, hleft, hright]

/-- Equality of actual maps is faithfully reflected in their finite matrices. -/
theorem mapMatrix_injective (p : FiniteRetract P) (q : FiniteRetract Q) :
    Function.Injective (p.mapMatrix q) := by
  intro f g h
  have hh := congrArg (p.mapOfMatrix q) h
  simpa only [mapOfMatrix_mapMatrix] using hh

end FiniteRetract
end
end Decoupling.HighDim.StableFree.Effective
