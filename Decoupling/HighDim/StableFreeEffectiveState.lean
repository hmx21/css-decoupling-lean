import Decoupling.HighDim.StableFreeEffectiveTower
import Decoupling.HighDim.StableFreeEffectiveArrows

/-!
# Executable Schanuel state and its exact mathematical interpretation

Only dense arrays and natural dimensions are runtime data. The actual
modules, injections, projective retractions and equivalence are semantic
witnesses in Prop; they supply no chosen matrix to the algorithm.
-/

namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic
universe u
variable {K : Type u} [Field K] {D h h₀ length s t p q : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

structure EmbeddedArrays (K : Type u) (D s t p q h : ℕ) where
  leftProjector : DenseMatrix K D p p h
  rightProjector : DenseMatrix K D q q h
  forward : DenseMatrix K D (t+q) (s+p) h
  inverse : DenseMatrix K D (s+p) (t+q) h

/-- Fixed-size version of an actual embedding, avoiding runtime casts. -/
structure EmbeddingAt {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (n : ℕ) where
  map : M →ₗ[R] Power R n
  injective : Function.Injective map

/-- Fixed-size actual retract; no basis of the projective module is required. -/
structure RetractAt {R : Type u} [CommRing R] (P : ModuleCat.{u} R) (n : ℕ) where
  embed : P →ₗ[R] Power R n
  project : Power R n →ₗ[R] P
  retract : project.comp embed = LinearMap.id

namespace EmbeddingAt
variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R} {n : ℕ}
abbrev model (m : EmbeddingAt M n) : FiniteEmbedding M := ⟨n,m.map,m.injective⟩
end EmbeddingAt
namespace RetractAt
variable {R : Type u} [CommRing R] {P : ModuleCat.{u} R} {n : ℕ}
abbrev model (p : RetractAt P n) : FiniteRetract P := ⟨n,p.embed,p.project,p.retract⟩
end RetractAt

/-- Full semantic meaning of a runtime state. All differential matrices refer
to the actual kernels, and both stored maps refer to the actual equivalence. -/
structure StateWitness (F : DenseTower K D h₀ length s) (G : DenseTower K D h₀ length t)
    (data : EmbeddedArrays K D s t p q h) where
  M : ModuleCat.{u} (Laurent K D)
  N : ModuleCat.{u} (Laurent K D)
  P : ModuleCat.{u} (Laurent K D)
  Q : ModuleCat.{u} (Laurent K D)
  m : EmbeddingAt M s
  n : EmbeddingAt N t
  left : RetractAt P p
  right : RetractAt Q q
  leftResolution : F.Models M m.map
  rightResolution : G.Models N n.map
  equiv : EmbeddedEquiv m.model n.model left.model right.model
  left_eq : matrixDenote data.leftProjector = left.model.projector
  right_eq : matrixDenote data.rightProjector = right.model.projector
  forward_eq : matrixDenote data.forward = equiv.forward
  inverse_eq : matrixDenote data.inverse = equiv.inverse

/-- Validity is a proposition. Eliminating it can prove solvability, but
cannot select runtime matrices from the hidden mathematical witnesses. -/
def StateValid (F : DenseTower K D h₀ length s) (G : DenseTower K D h₀ length t)
    (data : EmbeddedArrays K D s t p q h) : Prop := Nonempty (StateWitness F G data)

end Decoupling.HighDim.StableFree.Effective
