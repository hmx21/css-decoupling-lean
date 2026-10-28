import Decoupling.HighDim.StableFreeEffectiveStageCorrect
import Decoupling.HighDim.StableFreeEffectiveReindex

/-!
# Executable generalized Schanuel recursion

Every nonterminal level executes two complete Laurent lifting solves and
the displayed dense update programs. The returned arrays are reindexed by
fixed permutations; zero-length resolutions use the actual terminal blocks.
No recursive matrix, finite generating set or cost bound is an input.
-/

namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic ArithmeticCost
variable {K : Type*} [Field K] {D h₀ length s t : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

structure StableArrays (K : Type*) (D p q A B h : ℕ) where
  forward : DenseMatrix K D (q+B) (p+A) h
  inverse : DenseMatrix K D (p+A) (q+B) h
  /-- Rows, columns, input box at each executed complete Laurent solve. -/
  solverSystems : List (ℕ × ℕ × ℕ) := []

namespace DenseTower

def outputBox : {length s t : ℕ} → DenseTower K D h₀ length s → DenseTower K D h₀ length t →
    ℕ → ℕ → ℕ → ℕ
  | _, _, _, .zero _, .zero _, _, _, h => h
  | _, s, _, .step a _ F, .step b _ G, p, q, h =>
      outputBox F G (b+q) (a+p) (nextStageBox D s a b p q h)

/-- Exact arithmetic count for the two dense Schanuel update formulas. -/
def updateCost (D a b p q h : ℕ) : ℕ :=
  ((b+q)*(a+(b+q))*(a+p)*boxSize D (h+h)*(2*boxSize D h+1) +
    (b+q)*(a+(b+q))*boxSize D (h+h)) +
  ((b+q)*b*boxSize D h +
    ((a+p)*(b+(a+p))*(b+q)*boxSize D (h+h)*(2*boxSize D h+1) +
      (a+p)*(b+(a+p))*boxSize D (h+h)))

/-- Fully explicit cost recurrence, using only the supplied ranks, input
box, dimension and the proved complete solver's fixed search bound. -/
def costBound : {length s t : ℕ} → DenseTower K D h₀ length s → DenseTower K D h₀ length t →
    ℕ → ℕ → ℕ → ℕ
  | _, _, _, .zero _, .zero _, _, _, _ => 0
  | _, s, t, .step a _ F, .step b _ G, p, q, h =>
      (s+p)*(b+q)*(t+q)*boxSize D (h+h)*(2*boxSize D h+1) +
      (liftSolveCost D (s+p) 0 (a+p) (b+q) (h+h) +
        liftSolveCost D (s+p) 0 (b+q) (a+p) (h+h)) +
      updateCost D a b p q (stageLiftBox D (s+p) (a+p) (b+q) (h+h)) +
      costBound F G (b+q) (a+p) (nextStageBox D s a b p q h)

end DenseTower

variable [DecidableEq K]

/-- The actual recursion. Its validity argument is erased and is used only
to prove that each of the two concrete solver calls returns a solution. -/
def stabilizeProgram : {length s t : ℕ} →
    (F : DenseTower K D h₀ length s) → (G : DenseTower K D h₀ length t) →
    {p q h : ℕ} → (data : EmbeddedArrays K D s t p q h) →
    h₀ ≤ h → StateValid F G data →
    Work K (StableArrays K D p q (DenseTower.ranks F G).1 (DenseTower.ranks F G).2
      (DenseTower.outputBox F G p q h))
  | _, _, _, .zero _, .zero _, _, _, _, data, _, _ => Work.pure {
      forward := bottomBlockDense data.forward
      inverse := bottomBlockDense data.inverse }
  | _, s, _, .step a A F, .step b B G, p, q, _h, data, hh, hv =>
      let prepared := prepareStage A B data
      let solved := solveStage prepared.value (prepareStage_solvable A B F G data hh hv)
      let updated := updateStage data solved.value.1 solved.value.2
      let recursive := stabilizeProgram F G updated.value
        (hh.trans (Nat.le_max_left _ _))
        (updateStage_valid A B F G data hh hv _)
      Work.bind prepared fun _ => Work.bind solved fun _ => Work.bind updated fun _ =>
        Work.bind recursive fun out => Work.pure {
          forward := reindexDense out.inverse
            (collectOrder q b (DenseTower.ranks F G).1)
            (collectOrder p a (DenseTower.ranks F G).2)
          inverse := reindexDense out.forward
            (collectOrder p a (DenseTower.ranks F G).2)
            (collectOrder q b (DenseTower.ranks F G).1)
          solverSystems := (((s+p)+((a+p)+(a+p)))*(b+q),(a+p)*(b+q),_h+_h) ::
            (((s+p)+((b+q)+(b+q)))*(a+p),(b+q)*(a+p),_h+_h) :: out.solverSystems }

omit [DecidableEq K] in
theorem updateStage_cost {a b p q h : ℕ} (data : EmbeddedArrays K D s t p q h)
    (U : DenseMatrix K D (a+p) (b+q) (stageLiftBox D (s+p) (a+p) (b+q) (h+h)))
    (V : DenseMatrix K D (b+q) (a+p) (stageLiftBox D (s+p) (a+p) (b+q) (h+h))) :
    (updateStage data U V).cost = DenseTower.updateCost D a b p q
      (stageLiftBox D (s+p) (a+p) (b+q) (h+h)) := by
  simp only [updateStage,Work.bind_cost,Work.pure_cost,add_zero,
    stepForwardProgram_cost,stepInverseProgram_cost,DenseTower.updateCost]

theorem stabilizeProgram_cost (F : DenseTower K D h₀ length s) (G : DenseTower K D h₀ length t)
    {p q h : ℕ} (data : EmbeddedArrays K D s t p q h) (hh : h₀ ≤ h) (hv : StateValid F G data) :
    (stabilizeProgram F G data hh hv).cost ≤ DenseTower.costBound F G p q h := by
  induction F generalizing t p q h with
  | zero => cases G; simp only [stabilizeProgram,Work.pure_cost,DenseTower.costBound,Nat.le_refl]
  | step a A F ih =>
      cases G with
      | step b B G =>
        simp only [stabilizeProgram,Work.bind_cost,Work.pure_cost,add_zero,
          prepareStage_cost,updateStage_cost,DenseTower.costBound]
        have hsolve := solveStage_cost (prepareStage A B data).value
          (prepareStage_solvable A B F G data hh hv)
        have hrec := ih G
          (updateStage data
            (solveStage (prepareStage A B data).value (prepareStage_solvable A B F G data hh hv)).value.1
            (solveStage (prepareStage A B data).value (prepareStage_solvable A B F G data hh hv)).value.2).value
          (hh.trans (Nat.le_max_left _ _)) (updateStage_valid A B F G data hh hv _)
        omega


/-- Exactly two real solver callsites are executed at each nonterminal level. -/
theorem stabilizeProgram_solver_count (F : DenseTower K D h₀ length s) (G : DenseTower K D h₀ length t)
    {p q h : ℕ} (data : EmbeddedArrays K D s t p q h) (hh : h₀ ≤ h) (hv : StateValid F G data) :
    (stabilizeProgram F G data hh hv).value.solverSystems.length = 2*length := by
  induction F generalizing t p q h with
  | zero => cases G; rfl
  | step a A F ih =>
    cases G with
    | step b B G =>
      simp only [stabilizeProgram,Work.bind_value,Work.pure_value,List.length_cons]
      rw [ih]
      omega

end Decoupling.HighDim.StableFree.Effective
