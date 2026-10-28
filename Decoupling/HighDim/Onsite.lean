import Decoupling.HighDim.ShearCompile
import Mathlib.GroupTheory.Perm.Sign

/-!
# On-site SWAP gates and mixed SUM/SWAP circuits

SWAP is an independent gate primitive acting by `(a,b) ↦ (b,a)` at each
cell. No characteristic-two three-CNOT identity is used. Its site pairs
are disjoint and its Laurent action is proved to permute coefficients.
Finite species permutations are decomposed into a finite list of these
SWAP layers. `Layer` and `wordX`/`wordZ` then combine actual weighted SUM
and SWAP layers in a common finite circuit representation.
-/

noncomputable section

namespace Decoupling.HighDim.Circuit

open Matrix

variable {K : Type*} [CommRing K] {D : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A permutation matrix maps input species `j` to output species `σ j`. -/
def permMatrix (σ : Equiv.Perm ι) : Matrix ι ι (Laurent K D) :=
  (1 : Matrix ι ι (Laurent K D)).submatrix σ.symm id

omit [Fintype ι] in
theorem permMatrix_apply (σ : Equiv.Perm ι) (i j : ι) :
    permMatrix (K := K) (D := D) σ i j = if i = σ j then 1 else 0 := by
  simp [permMatrix, Matrix.one_apply, Equiv.symm_apply_eq]

@[simp] theorem permMatrix_mulVec (σ : Equiv.Perm ι) (p : ι → Laurent K D) :
    permMatrix σ *ᵥ p = p ∘ σ.symm := by
  simpa [permMatrix] using
    (Matrix.submatrix_mulVec_equiv (1 : Matrix ι ι (Laurent K D)) p σ.symm (Equiv.refl ι))

omit [Fintype ι] in
@[simp] theorem permMatrix_one : permMatrix (K := K) (D := D) (1 : Equiv.Perm ι) = 1 := rfl

theorem permMatrix_mul (σ τ : Equiv.Perm ι) :
    permMatrix (K := K) (D := D) (σ * τ) = permMatrix σ * permMatrix τ := by
  apply Matrix.ext_iff_mulVec.mpr
  intro p
  simp only [← Matrix.mulVec_mulVec, permMatrix_mulVec]
  rfl

omit [Fintype ι] in
theorem dagger_permMatrix (σ : Equiv.Perm ι) :
    dagger (permMatrix (K := K) (D := D) σ) = permMatrix σ.symm := by
  ext i j
  simp [dagger, permMatrix_apply, Equiv.eq_symm_apply, eq_comm]

theorem permMatrix_preserves_pairing (σ : Equiv.Perm ι) :
    dagger (permMatrix (K := K) (D := D) σ) * permMatrix σ = 1 := by
  rw [dagger_permMatrix, ← permMatrix_mul]
  change permMatrix (K := K) (D := D) (σ⁻¹ * σ) = 1
  rw [inv_mul_cancel, permMatrix_one]

/-- An on-site SWAP layer, exchanging two distinct species at every cell. -/
structure SWAP (ι : Type*) where
  left : ι
  right : ι
  distinct : left ≠ right

namespace SWAP

variable (g : SWAP ι)

def source (n : Translation D) : ι × Translation D := (g.left, n)
def destination (n : Translation D) : ι × Translation D := (g.right, n)

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
theorem distinct_sites (n : Translation D) : g.source n ≠ g.destination n :=
  fun h => g.distinct (congrArg Prod.fst h)

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
theorem disjoint_gates {n m : Translation D} (hne : n ≠ m) :
    g.source n ≠ g.source m ∧ g.source n ≠ g.destination m ∧
    g.destination n ≠ g.source m ∧ g.destination n ≠ g.destination m := by
  exact ⟨fun h => hne (congrArg Prod.snd h),
    fun h => g.distinct (congrArg Prod.fst h),
    fun h => g.distinct (congrArg Prod.fst h).symm,
    fun h => hne (congrArg Prod.snd h)⟩

def localAction (a b : K) : K × K := (b, a)

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
theorem local_involutive (a b : K) :
    localAction (localAction a b).1 (localAction a b).2 = (a, b) := rfl

def matrix : Matrix ι ι (Laurent K D) := permMatrix (Equiv.swap g.left g.right)

def config (p : ι → Translation D → K) (i : ι) (n : Translation D) : K :=
  p (Equiv.swap g.left g.right i) n

omit [CommRing K] [Fintype ι] in
theorem config_pair (p : ι → Translation D → K) (n : Translation D) :
    (g.config p g.left n, g.config p g.right n) =
      localAction (p g.left n) (p g.right n) := by
  simp [config, localAction]

omit [CommRing K] [Fintype ι] in
theorem config_untouched (p : ι → Translation D → K) (i : ι)
    (hl : i ≠ g.left) (hr : i ≠ g.right) (n : Translation D) :
    g.config p i n = p i n := by
  simp [config, Equiv.swap_apply_of_ne_of_ne hl hr]

theorem support (p : ι → Laurent K D) (i : ι) (n : Translation D) :
    ((g.matrix *ᵥ p) i).coeff n = g.config (fun j => (p j).coeff) i n := by
  simp [matrix, config]

theorem matrix_involutive : g.matrix (K := K) (D := D) * g.matrix = 1 := by
  rw [matrix, ← permMatrix_mul]
  simp

theorem preserves_pairing : dagger (g.matrix (K := K) (D := D)) * g.matrix = 1 :=
  permMatrix_preserves_pairing _

omit [CommRing K] [Fintype ι] in
theorem translation_covariant (b : Translation D) (p : ι → Translation D → K) :
    g.config (SUM.translateConfig b p) = SUM.translateConfig b (g.config p) := rfl

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
theorem translate_sites (n b : Translation D) :
    g.source (n + b) = (g.left, (g.source n).2 + b) ∧
    g.destination (n + b) = (g.right, (g.destination n).2 + b) := ⟨rfl, rfl⟩

end SWAP

def swapAction (c : List (SWAP ι)) : Matrix ι ι (Laurent K D) :=
  (c.map SWAP.matrix).prod

@[simp] theorem swapAction_nil : swapAction (K := K) (D := D) ([] : List (SWAP ι)) = 1 := rfl
@[simp] theorem swapAction_cons (g : SWAP ι) (c : List (SWAP ι)) :
    swapAction (K := K) (D := D) (g :: c) = g.matrix * swapAction c := rfl

/-- Every permutation of finitely many species is a finite sequence of
actual on-site SWAP layers, also for the empty species type. -/
theorem permutation_compilation (σ : Equiv.Perm ι) :
    ∃ c : List (SWAP ι), swapAction (K := K) (D := D) c = permMatrix σ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨[], rfl⟩
  | swap_mul σ i j hij ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨⟨i, j, hij⟩ :: c, ?_⟩
    rw [swapAction_cons, hc, permMatrix_mul]
    rfl

/-- Each constructor has independently proved local site and support semantics. -/
inductive Layer (K : Type*) (D : ℕ) (ι : Type*) where
  | sum : SUM K D ι → Layer K D ι
  | swap : SWAP ι → Layer K D ι

namespace Layer

def xMatrix : Layer K D ι → Matrix ι ι (Laurent K D)
  | .sum g => g.xMatrix
  | .swap g => g.matrix

def zMatrix : Layer K D ι → Matrix ι ι (Laurent K D)
  | .sum g => g.zMatrix
  | .swap g => g.matrix

def displacement : Layer K D ι → Translation D
  | .sum g => g.displacement
  | .swap _ => 0

def source : Layer K D ι → Translation D → ι × Translation D
  | .sum g => g.source
  | .swap g => g.source

def destination : Layer K D ι → Translation D → ι × Translation D
  | .sum g => g.destination
  | .swap g => g.destination

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
theorem distinct_sites (g : Layer K D ι) (n : Translation D) :
    g.source n ≠ g.destination n := by
  cases g with
  | sum g => exact g.distinct_sites n
  | swap g => exact g.distinct_sites n

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
theorem site_displacement (g : Layer K D ι) (n : Translation D) :
    (g.destination n).2 - (g.source n).2 = g.displacement := by
  cases g <;> simp [source, destination, displacement, SUM.source,
    SUM.destination, SWAP.source, SWAP.destination]

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
theorem disjoint_gates (g : Layer K D ι) {n m : Translation D} (hne : n ≠ m) :
    g.source n ≠ g.source m ∧ g.source n ≠ g.destination m ∧
    g.destination n ≠ g.source m ∧ g.destination n ≠ g.destination m := by
  cases g with
  | sum g => exact g.disjoint_gates hne
  | swap g => exact g.disjoint_gates hne

theorem preserves_pairing (g : Layer K D ι) : dagger g.xMatrix * g.zMatrix = 1 := by
  cases g with
  | sum g => exact g.preserves_pairing
  | swap g => exact g.preserves_pairing

def xConfig (g : Layer K D ι) : (ι → Translation D → K) → (ι → Translation D → K) :=
  match g with
  | .sum h => h.xConfig
  | .swap h => h.config

def zConfig (g : Layer K D ι) : (ι → Translation D → K) → (ι → Translation D → K) :=
  match g with
  | .sum h => h.zConfig
  | .swap h => h.config

theorem x_support (g : Layer K D ι) (p : ι → Laurent K D) (i : ι) (n : Translation D) :
    ((g.xMatrix *ᵥ p) i).coeff n = g.xConfig (fun j => (p j).coeff) i n := by
  cases g with
  | sum g => exact g.x_support p i n
  | swap g => exact g.support p i n

theorem z_support (g : Layer K D ι) (p : ι → Laurent K D) (i : ι) (n : Translation D) :
    ((g.zMatrix *ᵥ p) i).coeff n = g.zConfig (fun j => (p j).coeff) i n := by
  cases g with
  | sum g => exact g.z_support p i n
  | swap g => exact g.support p i n

omit [Fintype ι] in
theorem x_translation_covariant (g : Layer K D ι) (b : Translation D)
    (p : ι → Translation D → K) :
    g.xConfig (SUM.translateConfig b p) = SUM.translateConfig b (g.xConfig p) := by
  cases g with
  | sum g => exact g.x_translation_covariant b p
  | swap g => exact g.translation_covariant b p

omit [Fintype ι] in
theorem z_translation_covariant (g : Layer K D ι) (b : Translation D)
    (p : ι → Translation D → K) :
    g.zConfig (SUM.translateConfig b p) = SUM.translateConfig b (g.zConfig p) := by
  cases g with
  | sum g => exact g.z_translation_covariant b p
  | swap g => exact g.translation_covariant b p

end Layer

def wordX (c : List (Layer K D ι)) : Matrix ι ι (Laurent K D) := (c.map Layer.xMatrix).prod
def wordZ (c : List (Layer K D ι)) : Matrix ι ι (Laurent K D) := (c.map Layer.zMatrix).prod

/-- Actual composition of cellwise X-label layer transformations. -/
def wordXConfig : List (Layer K D ι) → (ι → Translation D → K) → (ι → Translation D → K)
  | [], p => p
  | g :: c, p => g.xConfig (wordXConfig c p)

/-- Actual composition of cellwise Z-label layer transformations. -/
def wordZConfig : List (Layer K D ι) → (ι → Translation D → K) → (ι → Translation D → K)
  | [], p => p
  | g :: c, p => g.zConfig (wordZConfig c p)

@[simp] theorem wordX_nil : wordX ([] : List (Layer K D ι)) = 1 := rfl
@[simp] theorem wordZ_nil : wordZ ([] : List (Layer K D ι)) = 1 := rfl
@[simp] theorem wordX_cons (g : Layer K D ι) (c : List (Layer K D ι)) :
    wordX (g :: c) = g.xMatrix * wordX c := rfl
@[simp] theorem wordZ_cons (g : Layer K D ι) (c : List (Layer K D ι)) :
    wordZ (g :: c) = g.zMatrix * wordZ c := rfl

theorem wordX_append (c d : List (Layer K D ι)) :
    wordX (c ++ d) = wordX c * wordX d := by simp [wordX]
theorem wordZ_append (c d : List (Layer K D ι)) :
    wordZ (c ++ d) = wordZ c * wordZ d := by simp [wordZ]

/-- Matrix multiplication agrees with the composition of actual local
X-label operations on every lattice coefficient. -/
theorem wordX_support (c : List (Layer K D ι)) (p : ι → Laurent K D)
    (i : ι) (n : Translation D) :
    ((wordX c *ᵥ p) i).coeff n = wordXConfig c (fun j => (p j).coeff) i n := by
  induction c generalizing i n with
  | nil => simp [wordXConfig]
  | cons g c ih =>
    rw [wordX_cons, ← Matrix.mulVec_mulVec, g.x_support]
    have h : (fun j a => ((wordX c *ᵥ p) j).coeff a) =
        wordXConfig c (fun j => (p j).coeff) := by
      funext j a
      exact ih j a
    rw [h]
    rfl

theorem wordZ_support (c : List (Layer K D ι)) (p : ι → Laurent K D)
    (i : ι) (n : Translation D) :
    ((wordZ c *ᵥ p) i).coeff n = wordZConfig c (fun j => (p j).coeff) i n := by
  induction c generalizing i n with
  | nil => simp [wordZConfig]
  | cons g c ih =>
    rw [wordZ_cons, ← Matrix.mulVec_mulVec, g.z_support]
    have h : (fun j a => ((wordZ c *ᵥ p) j).coeff a) =
        wordZConfig c (fun j => (p j).coeff) := by
      funext j a
      exact ih j a
    rw [h]
    rfl

omit [Fintype ι] in
theorem wordX_translation_covariant (c : List (Layer K D ι)) (b : Translation D)
    (p : ι → Translation D → K) :
    wordXConfig c (SUM.translateConfig b p) = SUM.translateConfig b (wordXConfig c p) := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    simp only [wordXConfig]
    rw [ih, g.x_translation_covariant]

omit [Fintype ι] in
theorem wordZ_translation_covariant (c : List (Layer K D ι)) (b : Translation D)
    (p : ι → Translation D → K) :
    wordZConfig c (SUM.translateConfig b p) = SUM.translateConfig b (wordZConfig c p) := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    simp only [wordZConfig]
    rw [ih, g.z_translation_covariant]

theorem wordZ_sum (c : List (SUM K D ι)) : wordZ (c.map Layer.sum) = zAction c := by
  simp [wordZ, zAction, List.map_map, Function.comp_def, Layer.zMatrix]

theorem wordZ_swap (c : List (SWAP ι)) :
    wordZ (K := K) (D := D) (c.map Layer.swap) = swapAction c := by
  simp [wordZ, swapAction, List.map_map, Function.comp_def, Layer.zMatrix]

theorem word_preserves_pairing (c : List (Layer K D ι)) :
    dagger (wordX c) * wordZ c = 1 := by
  induction c with
  | nil => simp
  | cons g c ih =>
    simp only [wordX_cons, wordZ_cons, dagger_mul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (dagger g.xMatrix),
      g.preserves_pairing, Matrix.one_mul, ih]

theorem wordX_eq_dagger_inverse (c : List (Layer K D ι))
    (A B : Matrix ι ι (Laurent K D)) (hZ : wordZ c = A) (hAB : A * B = 1) :
    wordX c = dagger B := by
  have h : dagger (wordX c) = B := by
    calc
      dagger (wordX c) = dagger (wordX c) * (A * B) := by rw [hAB, Matrix.mul_one]
      _ = (dagger (wordX c) * A) * B := (Matrix.mul_assoc _ _ _).symm
      _ = B := by rw [← hZ, word_preserves_pairing, Matrix.one_mul]
  simpa only [dagger_dagger] using congrArg dagger h

def wordRangeBound (c : List (Layer K D ι)) : ℕ :=
  c.foldr (fun g b => max (Finset.univ.sup (fun i => (g.displacement i).natAbs)) b) 0

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
theorem displacement_le_wordRangeBound (c : List (Layer K D ι)) (g : Layer K D ι)
    (hg : g ∈ c) (i : Fin D) : (g.displacement i).natAbs ≤ wordRangeBound c := by
  induction c with
  | nil => simp at hg
  | cons h c ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · exact le_trans (Finset.le_sup (f := fun j => (g.displacement j).natAbs)
        (Finset.mem_univ i)) (Nat.le_max_left _ _)
    · exact le_trans (ih hg) (Nat.le_max_right _ _)

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
theorem word_finite_depth_range (c : List (Layer K D ι)) :
    ∃ depth range : ℕ, depth = c.length ∧
      ∀ g ∈ c, ∀ i : Fin D, (g.displacement i).natAbs ≤ range :=
  ⟨c.length, wordRangeBound c, rfl, fun g hg i => displacement_le_wordRangeBound c g hg i⟩

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
/-- The bound applies to the distance between actual paired lattice sites,
not merely to a label stored in the circuit data. -/
theorem site_distance_le_wordRangeBound (c : List (Layer K D ι)) (g : Layer K D ι)
    (hg : g ∈ c) (n : Translation D) (i : Fin D) :
    (((g.destination n).2 - (g.source n).2) i).natAbs ≤ wordRangeBound c := by
  rw [g.site_displacement]
  exact displacement_le_wordRangeBound c g hg i

end Decoupling.HighDim.Circuit
