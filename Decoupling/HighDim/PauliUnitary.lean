import Decoupling.HighDim.Onsite
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Genuine qudit permutation unitaries and Pauli conjugation

The computational basis is indexed by finite-field configurations.  A bijective
finite-field linear map acts by an actual permutation of that basis, producing both
a complex unitary matrix and a linear isometry of the finite Hilbert space.
Pure X and pure Z conjugation identities are exact, including their phases.
Source: `drafts/main.tex`, Sections II.A and IV.C. Local weighted SUM and
SWAP compatibility is established below; no infinite tensor product is postulated.
-/

namespace Decoupling.HighDim.PauliUnitary

open Matrix

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [NeZero p]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Config (p : ℕ) (ι : Type*) := ι → ZMod p
abbrev State (p : ℕ) (ι : Type*) := Config p ι → ℂ
abbrev Hilbert (p : ℕ) [NeZero p] (ι : Type*) [Fintype ι] := EuclideanSpace ℂ (Config p ι)

/-- The computational ket, in explicit complex coordinates. -/
def ket (s : Config p ι) : State p ι := Pi.single s 1

/-- The inverse in this definition makes the matrix send `|s⟩` to `|e s⟩`. -/
def permutation (e : Config p ι ≃ Config p ι) : Matrix (Config p ι) (Config p ι) ℂ :=
  Equiv.Perm.permMatrix ℂ e.symm

@[simp]
theorem permutation_apply (e : Config p ι ≃ Config p ι) (ψ : State p ι) (s : Config p ι) :
    (permutation e *ᵥ ψ) s = ψ (e.symm s) := by
  exact congrFun (Matrix.permMatrix_mulVec (R := ℂ) (v := ψ) e.symm) s

omit [NeZero p] [DecidableEq ι] in
@[simp]
theorem permutation_adjoint (e : Config p ι ≃ Config p ι) :
    (permutation e)ᴴ = permutation e.symm := by
  simp [permutation, Equiv.Perm.inv_def]

/-- Actual complex unitarity, rather than preservation of a finite-field support form. -/
theorem permutation_unitary (e : Config p ι ≃ Config p ι) :
    (permutation e)ᴴ * permutation e = 1 := by
  rw [permutation_adjoint]
  change Equiv.Perm.permMatrix ℂ e * Equiv.Perm.permMatrix ℂ e.symm = 1
  rw [← Matrix.permMatrix_mul]
  simp [Equiv.Perm.mul_def]

def permutationUnitary (e : Config p ι ≃ Config p ι) : Matrix.unitaryGroup (Config p ι) ℂ :=
  ⟨permutation e, Matrix.mem_unitaryGroup_iff'.mpr (permutation_unitary e)⟩

/-- The corresponding unitary on the actual finite-dimensional complex Hilbert space. -/
def hilbertPermutation (e : Config p ι ≃ Config p ι) : Hilbert p ι ≃ₗᵢ[ℂ] Hilbert p ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp]
theorem hilbertPermutation_apply (e : Config p ι ≃ Config p ι) (ψ : Hilbert p ι) (s : Config p ι) :
    hilbertPermutation e ψ s = (permutation e *ᵥ (fun t => ψ t)) s := by
  rw [permutation_apply]
  rfl

theorem permutation_ket (e : Config p ι ≃ Config p ι) (s : Config p ι) :
    permutation e *ᵥ ket s = ket (e s) := by
  funext t
  simp only [permutation_apply, ket, Pi.single_apply]
  simp only [e.symm_apply_eq]

/-- Translation of computational labels by the X support. -/
def translation (a : Config p ι) : Config p ι ≃ Config p ι where
  toFun s := s + a
  invFun s := s - a
  left_inv s := add_sub_cancel_right s a
  right_inv s := sub_add_cancel s a

def X (a : Config p ι) : Matrix (Config p ι) (Config p ι) ℂ := permutation (translation a)

/-- The canonical faithful p-th-root phase, exp(2π i b/p). -/
def phase (b : ZMod p) : ℂ := ZMod.stdAddChar b

@[simp] theorem phase_zero : phase (0 : ZMod p) = 1 := AddChar.map_zero_eq_one _

theorem phase_add (a b : ZMod p) : phase (a + b) = phase a * phase b :=
  AddChar.map_add_eq_mul _ _ _

theorem phase_injective : Function.Injective (phase (p := p)) :=
  ZMod.injective_stdAddChar

@[simp] theorem phase_eq_one (a : ZMod p) : phase a = 1 ↔ a = 0 := by
  rw [← phase_zero (p := p)]
  exact phase_injective.eq_iff

theorem phase_star_mul (b : ZMod p) : star (phase b) * phase b = 1 := by
  change star ((ZMod.toCircle b : Circle) : ℂ) * ((ZMod.toCircle b : Circle) : ℂ) = 1
  simpa using Complex.conj_mul' ((ZMod.toCircle b : Circle) : ℂ)

def Z (b : Config p ι) : Matrix (Config p ι) (Config p ι) ℂ :=
  Matrix.diagonal (fun s => phase (b ⬝ᵥ s))

@[simp]
theorem X_apply (a : Config p ι) (ψ : State p ι) (s : Config p ι) :
    (X a *ᵥ ψ) s = ψ (s - a) := permutation_apply _ _ _

@[simp]
theorem Z_apply (b : Config p ι) (ψ : State p ι) (s : Config p ι) :
    (Z b *ᵥ ψ) s = phase (b ⬝ᵥ s) * ψ s := Matrix.mulVec_diagonal _ _ _

theorem X_ket (a s : Config p ι) : X a *ᵥ ket s = ket (s + a) :=
  permutation_ket (translation a) s

theorem Z_ket (b s : Config p ι) : Z b *ᵥ ket s = phase (b ⬝ᵥ s) • ket s := by
  funext t
  by_cases h : t = s
  · subst t
    simp [ket]
  · simp [ket, h]


/-- Support addition is literal multiplication of pure X Paulis. -/
theorem X_add (a b : Config p ι) : X (a + b) = X a * X b := by
  apply Matrix.mulVec_injective
  funext ψ s
  simp only [← Matrix.mulVec_mulVec, X_apply]
  congr 1
  abel

/-- Support addition is literal multiplication of pure Z Paulis. -/
theorem Z_add (a b : Config p ι) : Z (a + b) = Z a * Z b := by
  apply Matrix.mulVec_injective
  funext ψ s
  simp only [← Matrix.mulVec_mulVec, Z_apply, add_dotProduct, phase_add, mul_assoc]

theorem X_unitary (a : Config p ι) : (X a)ᴴ * X a = 1 :=
  permutation_unitary (translation a)

theorem Z_unitary (b : Config p ι) : (Z b)ᴴ * Z b = 1 := by
  simp only [Z, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have h : (fun s : Config p ι => star (phase (b ⬝ᵥ s)) * phase (b ⬝ᵥ s)) = fun _ => 1 := by
    funext s
    exact phase_star_mul _
  change Matrix.diagonal (fun s : Config p ι => star (phase (b ⬝ᵥ s)) * phase (b ⬝ᵥ s)) = 1
  rw [h, Matrix.diagonal_one]

variable (U : Config p ι ≃ₗ[ZMod p] Config p ι)

/-- The literal inverse-transpose support action, in the column convention. -/
def inverseTranspose (b : Config p ι) : Config p ι :=
  (LinearMap.toMatrix' U.symm.toLinearMap)ᵀ *ᵥ b

omit [NeZero p] in
theorem inverseTranspose_pairing (b s : Config p ι) :
    inverseTranspose U b ⬝ᵥ s = b ⬝ᵥ U.symm s := by
  rw [dotProduct_comm]
  unfold inverseTranspose
  rw [Matrix.dotProduct_transpose_mulVec, LinearMap.toMatrix'_mulVec]
  rfl

/-- No extra sign occurs in conjugating a pure X Pauli. -/
theorem conjugate_X (a : Config p ι) :
    permutation U.toEquiv * X a * (permutation U.toEquiv)ᴴ = X (U a) := by
  apply Matrix.mulVec_injective
  funext ψ s
  simp only [← Matrix.mulVec_mulVec, permutation_adjoint, permutation_apply,
    X_apply, LinearEquiv.coe_toEquiv, Equiv.symm_symm]
  simp [map_sub]

/-- No extra sign occurs in conjugating a pure Z Pauli. -/
theorem conjugate_Z (b : Config p ι) :
    permutation U.toEquiv * Z b * (permutation U.toEquiv)ᴴ = Z (inverseTranspose U b) := by
  apply Matrix.mulVec_injective
  funext ψ s
  simp only [← Matrix.mulVec_mulVec, permutation_adjoint, permutation_apply,
    Z_apply, LinearEquiv.coe_toEquiv, Equiv.symm_symm]
  rw [inverseTranspose_pairing]
  simp



section SUM

variable (control target : ι) (weight : ZMod p)

/-- Finite weighted SUM in target-row/control-column convention. -/
def sumMatrix : Matrix ι ι (ZMod p) := 1 + Matrix.single target control weight

omit [NeZero p] in
theorem sumMatrix_apply (s : Config p ι) (i : ι) :
    (sumMatrix control target weight *ᵥ s) i =
      s i + if i = target then weight * s control else 0 := by
  simp [sumMatrix, Matrix.add_mulVec, Matrix.single_mulVec, Function.update_apply]

omit [NeZero p] [Fintype ι] in
theorem sumMatrix_transpose :
    (sumMatrix control target weight)ᵀ = sumMatrix target control weight := by
  ext i j
  simp [sumMatrix, Matrix.single, Matrix.one_apply, and_comm, eq_comm]

omit [NeZero p] in
theorem sumMatrix_inverse (h : control ≠ target) :
    sumMatrix control target weight * sumMatrix control target (-weight) = 1 := by
  have hz : Matrix.single target control weight * Matrix.single target control weight = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ h _
  have hn : sumMatrix control target (-weight) = 1 - Matrix.single target control weight := by
    simp [sumMatrix, sub_eq_add_neg, Matrix.single_neg]
  rw [hn]
  unfold sumMatrix
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hz,
    sub_zero, sub_add_cancel]

/-- Actual reversible finite computational-label operation. -/
def sumGate (h : control ≠ target) : Config p ι ≃ₗ[ZMod p] Config p ι where
  __ := (sumMatrix control target weight).mulVecLin
  invFun := (sumMatrix control target (-weight)).mulVec
  left_inv s := by
    change sumMatrix control target (-weight) *ᵥ (sumMatrix control target weight *ᵥ s) = s
    have hi := sumMatrix_inverse control target (-weight) h
    simpa only [neg_neg, Matrix.mulVec_mulVec, hi, Matrix.one_mulVec] using
      congrArg (fun M => M *ᵥ s) hi
  right_inv s := by
    change sumMatrix control target weight *ᵥ (sumMatrix control target (-weight) *ᵥ s) = s
    rw [Matrix.mulVec_mulVec, sumMatrix_inverse control target weight h, Matrix.one_mulVec]

omit [NeZero p] in
@[simp] theorem sumGate_apply (h : control ≠ target) (s : Config p ι) :
    sumGate control target weight h s = sumMatrix control target weight *ᵥ s := rfl

omit [NeZero p] in
theorem sumGate_inverseTranspose (h : control ≠ target) (b : Config p ι) :
    inverseTranspose (sumGate control target weight h) b =
      sumMatrix target control (-weight) *ᵥ b := by
  unfold inverseTranspose
  have hm : LinearMap.toMatrix' (sumGate control target weight h).symm.toLinearMap =
      sumMatrix control target (-weight) := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_toMatrix']
    ext s i
    rfl
  rw [hm, sumMatrix_transpose]

/-- Exact complex SUM conjugation on pure X Pauli operators. -/
theorem sumGate_conjugate_X (h : control ≠ target) (a : Config p ι) :
    permutation (sumGate control target weight h).toEquiv * X a *
      (permutation (sumGate control target weight h).toEquiv)ᴴ =
        X (sumMatrix control target weight *ᵥ a) :=
  conjugate_X (sumGate control target weight h) a

/-- Exact complex SUM conjugation on pure Z operators, including the negative weight. -/
theorem sumGate_conjugate_Z (h : control ≠ target) (b : Config p ι) :
    permutation (sumGate control target weight h).toEquiv * Z b *
      (permutation (sumGate control target weight h).toEquiv)ᴴ =
        Z (sumMatrix target control (-weight) *ᵥ b) := by
  rw [conjugate_Z, sumGate_inverseTranspose]

end SUM

section LatticeCompatibility

variable {D : ℕ} (g : Circuit.SUM (ZMod p) D ι)

/-- Restriction to one actual paired gate, ordered control then target. -/
def pairRestriction (n : Translation D) (f : ι → Translation D → ZMod p) : Config p Bool
  | false => f g.control n
  | true => f g.target (n + g.displacement)

omit [NeZero p] [Fintype ι] in
theorem pairRestriction_X (n : Translation D) (f : ι → Translation D → ZMod p) :
    sumMatrix false true g.weight *ᵥ pairRestriction g n f =
      pairRestriction g n (g.xConfig f) := by
  funext i
  cases i <;> simp [sumMatrix_apply, pairRestriction, Circuit.SUM.xConfig, g.distinct]

omit [NeZero p] [Fintype ι] in
theorem pairRestriction_Z (n : Translation D) (f : ι → Translation D → ZMod p) :
    sumMatrix true false (-g.weight) *ᵥ pairRestriction g n f =
      pairRestriction g n (g.zConfig f) := by
  funext i
  cases i <;> simp [sumMatrix_apply, pairRestriction, Circuit.SUM.zConfig,
    Ne.symm g.distinct, sub_eq_add_neg]

/-- The exact local complex X conjugation agrees with restricting the already
proved infinite-layer Laurent action to the two actual paired sites. -/
theorem local_SUM_X_compatible (n : Translation D) (a : ι → Laurent (ZMod p) D) :
    let U := permutation (sumGate false true g.weight Bool.false_ne_true).toEquiv
    U * X (pairRestriction g n (fun i => (a i).coeff)) * Uᴴ =
      X (pairRestriction g n (fun i => ((g.xMatrix *ᵥ a) i).coeff)) := by
  dsimp only
  rw [sumGate_conjugate_X, pairRestriction_X]
  congr 1
  funext i
  cases i <;> exact (g.x_support a _ _).symm

/-- The analogous exact Z compatibility preserves both the negative weight
and the reversed Laurent displacement. -/
theorem local_SUM_Z_compatible (n : Translation D) (b : ι → Laurent (ZMod p) D) :
    let U := permutation (sumGate false true g.weight Bool.false_ne_true).toEquiv
    U * Z (pairRestriction g n (fun i => (b i).coeff)) * Uᴴ =
      Z (pairRestriction g n (fun i => ((g.zMatrix *ᵥ b) i).coeff)) := by
  dsimp only
  rw [sumGate_conjugate_Z, pairRestriction_Z]
  congr 1
  funext i
  cases i <;> exact (g.z_support b _ _).symm

end LatticeCompatibility

section SWAP

variable (g : Circuit.SWAP ι)

/-- Computational-label SWAP fixes all other species in the same finite cell. -/
def swapGate : Config p ι ≃ₗ[ZMod p] Config p ι :=
  LinearEquiv.funCongrLeft (ZMod p) (ZMod p) (Equiv.swap g.left g.right)

omit [NeZero p] in
theorem swapGate_pairing (b s : Config p ι) :
    b ⬝ᵥ (swapGate g).symm s = swapGate g b ⬝ᵥ s := by
  change (∑ i, b i * s (Equiv.swap g.left g.right i)) =
    ∑ i, b (Equiv.swap g.left g.right i) * s i
  exact Fintype.sum_equiv (Equiv.swap g.left g.right) _ _ (fun i => by simp)

omit [NeZero p] in
theorem swapGate_inverseTranspose (b : Config p ι) :
    inverseTranspose (swapGate g) b = swapGate g b := by
  funext i
  have h := inverseTranspose_pairing (swapGate g) b (Pi.single i 1)
  rw [swapGate_pairing] at h
  simpa using h

theorem swapGate_conjugate_X (a : Config p ι) :
    permutation (swapGate g).toEquiv * X a * (permutation (swapGate g).toEquiv)ᴴ =
      X (swapGate g a) := conjugate_X (swapGate g) a

theorem swapGate_conjugate_Z (b : Config p ι) :
    permutation (swapGate g).toEquiv * Z b * (permutation (swapGate g).toEquiv)ᴴ =
      Z (swapGate g b) := by rw [conjugate_Z, swapGate_inverseTranspose]

variable {D : ℕ}

/-- Actual complex on-site SWAP agrees with the Laurent X-label layer at every cell. -/
theorem local_SWAP_X_compatible (n : Translation D) (a : ι → Laurent (ZMod p) D) :
    let U := permutation (swapGate g (p := p)).toEquiv
    U * X (fun i => (a i).coeff n) * Uᴴ =
      X (fun i => ((g.matrix *ᵥ a) i).coeff n) := by
  dsimp only
  rw [swapGate_conjugate_X]
  congr 1
  funext i
  exact (g.support a i n).symm

theorem local_SWAP_Z_compatible (n : Translation D) (b : ι → Laurent (ZMod p) D) :
    let U := permutation (swapGate g (p := p)).toEquiv
    U * Z (fun i => (b i).coeff n) * Uᴴ =
      Z (fun i => ((g.matrix *ᵥ b) i).coeff n) := by
  dsimp only
  rw [swapGate_conjugate_Z]
  congr 1
  funext i
  exact (g.support b i n).symm

end SWAP

section LayerCompatibility

variable {D : ℕ}

/-- Ordered embedding of one actual local pair of a mixed circuit layer. -/
def layerPair (g : Circuit.Layer (ZMod p) D ι) (n : Translation D) : Bool → ι × Translation D
  | false => g.source n
  | true => g.destination n

omit [NeZero p] [Fintype ι] [DecidableEq ι] in
theorem layerPair_injective (g : Circuit.Layer (ZMod p) D ι) (n : Translation D) :
    Function.Injective (layerPair g n) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exact False.elim (g.distinct_sites n h)
  · exact False.elim (g.distinct_sites n h.symm)
  · rfl

def layerPairRestriction (g : Circuit.Layer (ZMod p) D ι) (n : Translation D)
    (f : ι → Translation D → ZMod p) : Config p Bool :=
  fun b => f (layerPair g n b).1 (layerPair g n b).2

omit [NeZero p] [Fintype ι] [DecidableEq ι] in
theorem layerPairRestriction_sum (g : Circuit.SUM (ZMod p) D ι) (n : Translation D)
    (f : ι → Translation D → ZMod p) :
    layerPairRestriction (.sum g) n f = pairRestriction g n f := by
  funext b
  cases b <;> rfl

/-- A genuine two-qudit computational permutation for each SUM/SWAP layer member. -/
def layerLocalGate (g : Circuit.Layer (ZMod p) D ι) : Config p Bool ≃ₗ[ZMod p] Config p Bool :=
  match g with
  | .sum h => sumGate false true h.weight Bool.false_ne_true
  | .swap _ => swapGate ⟨false, true, Bool.false_ne_true⟩

def layerLocalUnitary (g : Circuit.Layer (ZMod p) D ι) : Matrix.unitaryGroup (Config p Bool) ℂ :=
  permutationUnitary (layerLocalGate g).toEquiv

omit [Fintype ι] in
theorem layerLocal_X_config (g : Circuit.Layer (ZMod p) D ι) (n : Translation D)
    (f : ι → Translation D → ZMod p) :
    permutation (layerLocalGate g).toEquiv * X (layerPairRestriction g n f) *
      (permutation (layerLocalGate g).toEquiv)ᴴ =
        X (layerPairRestriction g n (g.xConfig f)) := by
  cases g with
  | sum g =>
    simp only [layerLocalGate, layerPairRestriction_sum, Circuit.Layer.xConfig]
    rw [sumGate_conjugate_X, pairRestriction_X]
  | swap g =>
    rw [show layerLocalGate (Circuit.Layer.swap g) =
      swapGate (p := p) ⟨false, true, Bool.false_ne_true⟩ from rfl, swapGate_conjugate_X]
    congr 1
    funext b
    cases b <;> simp [swapGate, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft,
      layerPairRestriction, layerPair, Circuit.Layer.xConfig, Circuit.Layer.source,
      Circuit.Layer.destination, Circuit.SWAP.source, Circuit.SWAP.destination, Circuit.SWAP.config]

omit [Fintype ι] in
theorem layerLocal_Z_config (g : Circuit.Layer (ZMod p) D ι) (n : Translation D)
    (f : ι → Translation D → ZMod p) :
    permutation (layerLocalGate g).toEquiv * Z (layerPairRestriction g n f) *
      (permutation (layerLocalGate g).toEquiv)ᴴ =
        Z (layerPairRestriction g n (g.zConfig f)) := by
  cases g with
  | sum g =>
    simp only [layerLocalGate, layerPairRestriction_sum, Circuit.Layer.zConfig]
    rw [sumGate_conjugate_Z, pairRestriction_Z]
  | swap g =>
    rw [show layerLocalGate (Circuit.Layer.swap g) =
      swapGate (p := p) ⟨false, true, Bool.false_ne_true⟩ from rfl, swapGate_conjugate_Z]
    congr 1
    funext b
    cases b <;> simp [swapGate, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft,
      layerPairRestriction, layerPair, Circuit.Layer.zConfig, Circuit.Layer.source,
      Circuit.Layer.destination, Circuit.SWAP.source, Circuit.SWAP.destination, Circuit.SWAP.config]

/-- Uniform mixed-layer compatibility with the actual infinite-lattice Laurent labels. -/
theorem layerLocal_X_compatible (g : Circuit.Layer (ZMod p) D ι) (n : Translation D)
    (a : ι → Laurent (ZMod p) D) :
    permutation (layerLocalGate g).toEquiv *
      X (layerPairRestriction g n (fun i => (a i).coeff)) *
      (permutation (layerLocalGate g).toEquiv)ᴴ =
        X (layerPairRestriction g n (fun i => ((g.xMatrix *ᵥ a) i).coeff)) := by
  rw [layerLocal_X_config]
  congr 1
  funext b
  exact (g.x_support a _ _).symm

theorem layerLocal_Z_compatible (g : Circuit.Layer (ZMod p) D ι) (n : Translation D)
    (a : ι → Laurent (ZMod p) D) :
    permutation (layerLocalGate g).toEquiv *
      Z (layerPairRestriction g n (fun i => (a i).coeff)) *
      (permutation (layerLocalGate g).toEquiv)ᴴ =
        Z (layerPairRestriction g n (fun i => ((g.zMatrix *ᵥ a) i).coeff)) := by
  rw [layerLocal_Z_config]
  congr 1
  funext b
  exact (g.z_support a _ _).symm

end LayerCompatibility

end
end Decoupling.HighDim.PauliUnitary
