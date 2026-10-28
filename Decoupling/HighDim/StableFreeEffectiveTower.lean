import Decoupling.HighDim.StableFreeEffectiveBlockProgram

/-!
# Materialized finite-resolution towers and exact semantic models

The executable tower stores just ranks and dense differential arrays. Its
semantic predicate means that these arrays are the actual consecutive free
covers of the actual kernels. Existential module data occur only in Prop and
are not evaluated by the recursive matrix program.
-/

namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic
universe u
variable {K : Type u} [Field K] {D h : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

inductive DenseTower (K : Type u) (D h : ℕ) : ℕ → ℕ → Type u
  | zero (ambient : ℕ) : DenseTower K D h 0 ambient
  | step {length ambient : ℕ} (rank : ℕ) (head : DenseMatrix K D ambient rank h)
      (tail : DenseTower K D h length rank) : DenseTower K D h (length+1) ambient

namespace DenseTower

def rankSum : {length ambient : ℕ} → DenseTower K D h length ambient → ℕ
  | _, _, .zero _ => 0
  | _, _, .step rank _ tail => rank+rankSum tail

/-- The alternating free ranks are determined entirely by the actual input
free terms, including empty resolutions. -/
def ranks : {length s t : ℕ} → DenseTower K D h length s → DenseTower K D h length t → ℕ × ℕ
  | _, _, _, .zero _, .zero _ => (0,0)
  | _, _, _, .step a _ F, .step b _ G => (a+(ranks F G).2,b+(ranks F G).1)

omit [Field K] in
theorem ranks_sum {length s t : ℕ} (F : DenseTower K D h length s)
    (G : DenseTower K D h length t) : (ranks F G).1+(ranks F G).2 = rankSum F+rankSum G := by
  induction F generalizing t with
  | zero => cases G; rfl
  | step a A F ih =>
      cases G with
      | step b B G =>
          simp only [ranks,rankSum]
          have hi := ih G
          omega

/-- Each cover is onto its actual module and its stored differential is its
actual matrix in the specified ambient embedding. -/
inductive Models : {length ambient : ℕ} → DenseTower K D h length ambient →
    (M : ModuleCat.{u} (Laurent K D)) → (M →ₗ[Laurent K D] Power (Laurent K D) ambient) → Prop
  | zero {ambient} {M : ModuleCat.{u} (Laurent K D)}
      (emb : M →ₗ[Laurent K D] Power (Laurent K D) ambient)
      (hzero : ∀ x : M, x = 0) : Models (.zero ambient) M emb
  | step {length ambient rank} {head : DenseMatrix K D ambient rank h}
      {tail : DenseTower K D h length rank} {M : ModuleCat.{u} (Laurent K D)}
      {emb : M →ₗ[Laurent K D] Power (Laurent K D) ambient}
      (F : ModuleCat.{u} (Laurent K D)) (coordinates : F ≃ₗ[Laurent K D] Power (Laurent K D) rank)
      (cover : F →ₗ[Laurent K D] M) (surjective : Function.Surjective cover)
      (matrix_eq : matrixDenote head = LinearMap.toMatrix'
        (emb.comp (cover.comp coordinates.symm.toLinearMap)))
      (rest : Models tail (ModuleCat.of (Laurent K D) (LinearMap.ker cover))
        (coordinates.toLinearMap.comp (LinearMap.ker cover).subtype)) :
      Models (.step rank head tail) M emb

omit [Field K] in
/-- The budget is conserved when the two enlarged projective factors are
swapped and the current free terms are removed. -/
theorem budget_step {length s t a b : ℕ} (A : DenseMatrix K D s a h)
    (B : DenseMatrix K D t b h) (F : DenseTower K D h length a)
    (G : DenseTower K D h length b) (p q : ℕ) :
    (b+q)+(a+p)+rankSum F+rankSum G =
      p+q+rankSum (.step a A F)+rankSum (.step b B G) := by
  simp only [rankSum]
  omega

end DenseTower
end Decoupling.HighDim.StableFree.Effective
