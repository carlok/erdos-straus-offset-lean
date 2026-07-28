/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A Lean-verified offset construction for the Erdős–Straus equation

This file gives a self-contained, constructive formalization of an offset
construction for the Erdős–Straus equation
$$4/n = 1/x + 1/y + 1/z.$$

The construction packages the classical divisor split into a congruence
condition indexed by a prime `p ≡ 3 (mod 4)`.  For each admissible seed
`(p, d, n)` it produces explicit positive denominators `x, y, z` and proves the
equality in `ℚ`; admissibility then lifts to the whole arithmetic progression
`n + 4 * p * d * k`.  The file moreover characterizes *all* positive transport
steps `T` preserving admissibility, and proves that `4 * p * d` is the least
such step.

The Erdős–Straus conjecture itself remains open; this file makes no claim
toward resolving it.  The underlying divisor split is classical (Mordell;
Vaughan).

## Main definitions

* `IsES n x y z`: the proposition that `x, y, z` are positive natural-number
  denominators giving an Erdős–Straus representation of `n` (the equality is in
  `ℚ`).
* `offsetX p n`, `offsetB p n`: the offset denominator `(n + p) / 4` and the
  associated product `n * offsetX p n`.
* `OffsetAdmissible p d n`: the structure packaging the hypotheses under which
  the construction applies.

## Main results

* `constructive_offset`: for admissible `(p, d, n)`, the constructed
  denominators are positive, all divisions are exact, and the result is `IsES`.
* `OffsetAdmissible.add_period`: the step `4 * p * d` preserves admissibility.
* `OffsetAdmissible.all_add_mul_iff`: a positive step `T` preserves every
  transported seed iff `4 ∣ T`, `p ∣ T`, and two divisibility conditions on
  `offsetB` hold.
* `OffsetAdmissible.least_positive_period`: `4 * p * d` is the least positive
  transport period.

## References

* L. J. Mordell, *Diophantine Equations*, Academic Press, 1969.
* R. C. Vaughan, *On a problem of Erdős, Straus and Schinzel*, Mathematika 17
  (1970), 193–198.

## Tags

Erdős–Straus, Egyptian fractions, unit fractions, Diophantine equation,
arithmetic progression.
-/

@[expose] public section

namespace ErdosStraus

private lemma sq_nezero_int (q : ℤ) (hq : q ≠ 0) : q * q ≠ 0 := by
  intro h
  exact hq ((Int.mul_eq_zero.mp h).elim id id)

private theorem unified_offset_theorem (n x p b d1 d2 y z : ℤ)
    (h_x : 4 * x = n + p)
    (h_b : b = n * x)
    (h_d : d1 * d2 = b * b)
    (h_y : p * y = b + d1)
    (h_z : p * z = b + d2)
    (hp : p ≠ 0)
    : 4 * x * y * z = n * (x * y + x * z + y * z) := by
  -- It suffices to prove the goal scaled by p²; then cancel the nonzero p².
  suffices H : p * p * (4 * x * y * z) = p * p * (n * (x * y + x * z + y * z)) by
    exact mul_left_cancel₀ (sq_nezero_int p hp) H
  -- Eliminate b by definitional substitution (H2): b := n * x everywhere.
  subst b
  -- Left and right sides, rewritten via H4, H5; each step checked by `ring`.
  have L : p * p * (4 * x * y * z) = 4 * x * (n * x + d1) * (n * x + d2) := by
    rw [← h_y, ← h_z]; ring
  have R : p * p * (n * (x * y + x * z + y * z))
         = n * (x * p * (n * x + d1) + x * p * (n * x + d2) + (n * x + d1) * (n * x + d2)) := by
    rw [← h_y, ← h_z]; ring
  -- Substitute H1 (4x = n+p); the residual is exactly p·(d1·d2 − b²) = p·H3.
  rw [L, R, h_x]
  linear_combination p * h_d

/-! ## Positive natural-number formulation -/

/-- `IsES n x y z` means that `x,y,z` are positive natural-number denominators
giving an Erdős--Straus representation of the positive natural number `n`. -/
def IsES (n x y z : ℕ) : Prop :=
  0 < n ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- A positive natural-number solution of the cross-multiplied polynomial
identity gives the corresponding rational unit-fraction identity. -/
theorem isES_of_polynomial (n x y z : ℕ)
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hpoly : 4 * x * y * z = n * (x * y + x * z + y * z)) :
    IsES n x y z := by
  refine ⟨hn, hx, hy, hz, ?_⟩
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hx)
  have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hy)
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz)
  have hpolyq :
      (4 : ℚ) * x * y * z = n * (x * y + x * z + y * z) := by
    exact_mod_cast hpoly
  field_simp [hnq, hxq, hyq, hzq]
  ring_nf at hpolyq ⊢
  exact hpolyq

/-- Positive certificate theorem.  The five equational hypotheses are a
division-free certificate for an Erdős--Straus representation. -/
theorem isES_of_offset_certificate (n x p b d1 d2 y z : ℕ)
    (hn : 0 < n) (hx : 0 < x) (hp : 0 < p)
    (hy : 0 < y) (hz : 0 < z)
    (h_x : 4 * x = n + p)
    (h_b : b = n * x)
    (h_d : d1 * d2 = b * b)
    (h_y : p * y = b + d1)
    (h_z : p * z = b + d2) :
    IsES n x y z := by
  apply isES_of_polynomial n x y z hn hx hy hz
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hi := unified_offset_theorem
    (n : ℤ) (x : ℤ) (p : ℤ) (b : ℤ)
    (d1 : ℤ) (d2 : ℤ) (y : ℤ) (z : ℤ)
    (by exact_mod_cast h_x)
    (by exact_mod_cast h_b)
    (by exact_mod_cast h_d)
    (by exact_mod_cast h_y)
    (by exact_mod_cast h_z)
    hpz
  exact_mod_cast hi

/-- If the first factor is congruent to `-b` modulo a prime `p`, then so is
the complementary factor.  The proof performs cancellation in `ZMod p`. -/
theorem second_divisibility (p b d1 d2 : ℕ)
    (hp : Nat.Prime p)
    (hpb : ¬ p ∣ b)
    (hfactor : d1 * d2 = b * b)
    (hfirst : p ∣ b + d1) :
    p ∣ b + d2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hb0 : (b : ZMod p) ≠ 0 := by
    intro h
    exact hpb ((ZMod.natCast_eq_zero_iff b p).mp h)
  have hsum1 : ((b + d1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (b + d1) p).mpr hfirst
  have hd1 : (d1 : ZMod p) = -(b : ZMod p) := by
    push_cast at hsum1
    linear_combination hsum1
  have hd10 : (d1 : ZMod p) ≠ 0 := by
    rw [hd1]
    exact neg_ne_zero.mpr hb0
  have hfactor' : (d1 : ZMod p) * d2 = b * b := by
    simpa using congrArg (fun m : ℕ => (m : ZMod p)) hfactor
  have hd2 : (d2 : ZMod p) = -(b : ZMod p) := by
    apply mul_left_cancel₀ hd10
    calc
      (d1 : ZMod p) * d2 = b * b := hfactor'
      _ = (-b) * (-b) := by ring
      _ = (d1 : ZMod p) * (-b) := by rw [hd1]
  apply (ZMod.natCast_eq_zero_iff (b + d2) p).mp
  push_cast
  rw [hd2]
  exact add_neg_cancel _

/-- Fully constructive positive offset theorem.

For the displayed inputs, Lean constructs the denominators using natural-number
division, proves each division exact, proves positivity, and concludes the
rational Erdős--Straus identity.  The hypothesis `p ∣ b + d1` is the natural
number form of `d1 ≡ -b (mod p)`. -/
theorem constructive_offset (n p d1 : ℕ)
    (hn : 2 ≤ n)
    (hp : Nat.Prime p)
    (hp4 : p % 4 = 3)
    (hn4 : n % 4 = 1)
    (hpn : ¬ p ∣ n)
    (hd1 : 0 < d1)
    (hd1b : d1 ∣ n * ((n + p) / 4))
    (hfirst : p ∣ n * ((n + p) / 4) + d1) :
    let x := (n + p) / 4
    let b := n * x
    let d2 := b * b / d1
    let y := (b + d1) / p
    let z := (b + d2) / p
    IsES n x y z := by
  dsimp only
  let x := (n + p) / 4
  let b := n * x
  let d2 := b * b / d1
  let y := (b + d1) / p
  let z := (b + d2) / p
  have hp0 : 0 < p := hp.pos
  have hn0 : 0 < n := by omega
  have hfour : 4 ∣ n + p := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  have hxrel : 4 * x = n + p := by
    dsimp [x]
    exact Nat.mul_div_cancel' hfour
  have hx0 : 0 < x := by omega
  have hb0 : 0 < b := by
    dsimp [b]
    exact Nat.mul_pos hn0 hx0
  have hpx : ¬ p ∣ x := by
    intro h
    have hp4x : p ∣ 4 * x := dvd_mul_of_dvd_right h 4
    rw [hxrel] at hp4x
    exact hpn ((Nat.dvd_add_iff_left (dvd_refl p)).mpr hp4x)
  have hpb : ¬ p ∣ b := by
    intro h
    rcases hp.dvd_mul.mp (by simpa [b] using h) with h | h
    · exact hpn h
    · exact hpx h
  have hdprod : d1 ∣ b * b := by
    rcases hd1b with ⟨c, hc⟩
    refine ⟨c * b, ?_⟩
    dsimp [b, x] at hc ⊢
    rw [hc]
    ring
  have hfactor : d1 * d2 = b * b := by
    dsimp [d2]
    exact Nat.mul_div_cancel' hdprod
  have hsecond : p ∣ b + d2 :=
    second_divisibility p b d1 d2 hp hpb hfactor
      (by simpa [b, x] using hfirst)
  have hyrel : p * y = b + d1 := by
    dsimp [y]
    exact Nat.mul_div_cancel' (by simpa [b, x] using hfirst)
  have hzrel : p * z = b + d2 := by
    dsimp [z]
    exact Nat.mul_div_cancel' hsecond
  have hd20 : 0 < d2 := by
    by_contra h
    have hd2z : d2 = 0 := Nat.eq_zero_of_not_pos h
    rw [hd2z, mul_zero] at hfactor
    have : 0 < b * b := Nat.mul_pos hb0 hb0
    omega
  have hy0 : 0 < y := by
    apply Nat.pos_of_ne_zero
    intro hyz
    rw [hyz, mul_zero] at hyrel
    omega
  have hz0 : 0 < z := by
    apply Nat.pos_of_ne_zero
    intro hzz
    rw [hzz, mul_zero] at hzrel
    omega
  exact isES_of_offset_certificate n x p b d1 d2 y z
    hn0 hx0 hp0 hy0 hz0 hxrel rfl hfactor hyrel hzrel

/-! ## Packaged offset admissibility -/

/-- The offset denominator \(X_p(n)=(n+p)/4\). -/
@[reducible] def offsetX (p n : ℕ) : ℕ := (n + p) / 4

/-- The associated product \(B_p(n)=nX_p(n)\). -/
@[reducible] def offsetB (p n : ℕ) : ℕ := n * offsetX p n

/-- `OffsetAdmissible p d n` packages exactly the hypotheses of
`constructive_offset` for the fixed divisor `d`, as a structure rather than a
conjunction.  The fields are named so that anonymous-constructor syntax
`⟨hn, hp, hp4, hn4, hpn, hd, hdb, hfirst⟩` and `rcases ... with ⟨...⟩` work
exactly as for the equivalent conjunction. -/
structure OffsetAdmissible (p d n : ℕ) : Prop where
  /-- Lower bound on the represented integer. -/
  protected two_le : 2 ≤ n
  /-- The offset prime. -/
  protected prime : Nat.Prime p
  /-- The prime is congruent to `3` modulo `4`. -/
  protected p_mod_four : p % 4 = 3
  /-- The represented integer is congruent to `1` modulo `4`. -/
  protected n_mod_four : n % 4 = 1
  /-- The prime does not divide the represented integer. -/
  protected not_p_dvd_n : ¬ p ∣ n
  /-- The fixed divisor is positive. -/
  protected d_pos : 0 < d
  /-- The fixed divisor divides `offsetB p n`. -/
  protected d_dvd_B : d ∣ offsetB p n
  /-- The prime divides `offsetB p n + d`. -/
  protected p_dvd_B_add_d : p ∣ offsetB p n + d

namespace OffsetAdmissible

/-- An admissible offset constructs a positive Erdős--Straus representation.
This is a packaged invocation of `constructive_offset`. -/
theorem isES {p d n : ℕ} (h : OffsetAdmissible p d n) :
    let x := offsetX p n
    let b := offsetB p n
    let d2 := b * b / d
    let y := (b + d) / p
    let z := (b + d2) / p
    IsES n x y z := by
  rcases h with ⟨hn, hp, hp4, hn4, hpn, hd, hdb, hfirst⟩
  simpa [offsetX, offsetB] using
    constructive_offset n p d hn hp hp4 hn4 hpn hd hdb hfirst

end OffsetAdmissible

/-! ## Transport through a fixed-divisor period -/

/-- The offset denominator changes linearly under the period `4 * p * d`. -/
private theorem offsetX_add_period (p d n k : ℕ)
    (hp4 : p % 4 = 3) (hn4 : n % 4 = 1) :
    offsetX p (n + 4 * p * d * k) = offsetX p n + p * d * k := by
  have hfour : 4 ∣ n + p := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  have hbase : 4 * offsetX p n = n + p := by
    exact Nat.mul_div_cancel' hfour
  change (n + 4 * p * d * k + p) / 4 = (n + p) / 4 + p * d * k
  have hperiod : 4 * p * d * k = 4 * (p * d * k) := by ring
  rw [hperiod]
  omega

/-- Exact transport identity for the associated product `B_p`. -/
private theorem offsetB_add_period (p d n k : ℕ)
    (hp4 : p % 4 = 3) (hn4 : n % 4 = 1) :
    offsetB p (n + 4 * p * d * k) =
      offsetB p n +
        p * d * k * (n + 4 * offsetX p n + 4 * p * d * k) := by
  unfold offsetB
  rw [offsetX_add_period p d n k hp4 hn4]
  ring

namespace OffsetAdmissible

/-- Admissibility is preserved on adding any multiple of the period `4*p*d`. -/
theorem add_period {p d n : ℕ} (h : OffsetAdmissible p d n) (k : ℕ) :
    OffsetAdmissible p d (n + 4 * p * d * k) := by
  rcases h with ⟨hn, hp, hp4, hn4, hpn, hd, hdb, hfirst⟩
  have hperiod4 : 4 ∣ 4 * p * d * k := by
    refine ⟨p * d * k, ?_⟩
    ring
  have hperiodp : p ∣ 4 * p * d * k := by
    refine ⟨4 * d * k, ?_⟩
    ring
  have hB := offsetB_add_period p d n k hp4 hn4
  let q := n + 4 * offsetX p n + 4 * p * d * k
  have hdeltaD : d ∣ p * d * k * q := by
    refine ⟨p * k * q, ?_⟩
    ring
  have hdeltaP : p ∣ p * d * k * q := by
    refine ⟨d * k * q, ?_⟩
    ring
  refine ⟨by omega, hp, hp4, ?_, ?_, hd, ?_, ?_⟩
  · simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hperiod4, hn4]
  · intro hnew
    exact hpn ((Nat.dvd_add_iff_left hperiodp).mpr hnew)
  · rw [hB]
    exact Nat.dvd_add hdb (by simpa [q] using hdeltaD)
  · rw [hB]
    convert Nat.dvd_add hfirst (by simpa [q] using hdeltaP) using 1
    ring

end OffsetAdmissible

/-! ## General transport and period characterization

The lemmas `offsetX_add_period` and `offsetB_add_period` above establish transport
for the *specific* period `T = 4 * p * d * k`.  The results below work with an
arbitrary `T` divisible by four.  They are algebraic tools for a subsequent
characterization of transport periods; no novelty or minimality claim is made
by these identities alone. -/

/-- General transport identity for `offsetX`: for any `T` with `4 ∣ T`,
`offsetX(p, n+T) = offsetX(p,n) + T/4`.  (Identity A.) -/
theorem offsetX_add_general (p n T : ℕ) (hp4 : p % 4 = 3) (hn4 : n % 4 = 1)
    (hT : 4 ∣ T) :
    offsetX p (n + T) = offsetX p n + T / 4 := by
  have hfour_n : 4 ∣ n + p := by apply Nat.dvd_of_mod_eq_zero; omega
  have hfour_nT : 4 ∣ n + T + p := by omega
  have hbase : 4 * ((n + p) / 4) = n + p := Nat.mul_div_cancel' hfour_n
  have hnew : 4 * ((n + T + p) / 4) = n + T + p := Nat.mul_div_cancel' hfour_nT
  have hT4 : 4 * (T / 4) = T := Nat.mul_div_cancel' hT
  simp only [offsetX]
  omega

/-- General transport identity for `offsetB`: for any `T` with `4 ∣ T`, writing
`u = T/4`, `offsetB(p, n+T) = offsetB(p,n) + u*(n + 4*offsetX(p,n) + 4*u)`.
(Identity B.) -/
theorem offsetB_add_general (p n T : ℕ) (hp4 : p % 4 = 3) (hn4 : n % 4 = 1)
    (hT : 4 ∣ T) :
    offsetB p (n + T) =
      offsetB p n + (T / 4) * (n + 4 * offsetX p n + 4 * (T / 4)) := by
  -- Pull out u = T/4 with the exact equation 4*u = T, so `ring` sees no division.
  obtain ⟨u, hu⟩ : ∃ u : ℕ, 4 * u = T := ⟨T / 4, Nat.mul_div_cancel' hT⟩
  have hx := offsetX_add_general p n T hp4 hn4 hT
  simp only [offsetB, hx, show T / 4 = u from by omega]
  subst hu
  ring

/-- Polynomial-divisibility lemma: `d ∣ a₁*k + a₂*k²` for all `k ∈ ℕ` iff
`d ∣ (a₁+a₂)` and `d ∣ 2*a₂`.  (⟸ uses `k(k−1)` even; ⟹ evaluates at k=1,2.)
Standalone; used by the period-characterization theorem. -/
theorem poly_dvd_all (d a1 a2 : ℕ) :
    (∀ k : ℕ, d ∣ a1 * k + a2 * k * k) ↔ d ∣ (a1 + a2) ∧ d ∣ 2 * a2 := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨hs, h2⟩ k => ?_⟩
  · -- Evaluate at `k = 1`.
    have h1 : d ∣ a1 * 1 + a2 * 1 * 1 := h 1
    convert h1 using 1; ring
  · -- Subtract twice the value at `k = 1` from the value at `k = 2`.
    have h1 : d ∣ a1 + a2 := by
      convert h 1 using 1
      ring
    have h2k : d ∣ a1 * 2 + a2 * 2 * 2 := h 2
    have hdouble : d ∣ 2 * (a1 + a2) :=
      dvd_mul_of_dvd_right h1 2
    have hsub := Nat.dvd_sub h2k hdouble
    convert hsub using 1
    omega
  · -- For `k+1`, split off `(k+1)(a1+a2)`; the remaining product
    -- contains the even number `k(k+1)`.
    rcases k with _ | k
    · simp
    · have heq :
          a1 * (k + 1) + a2 * (k + 1) * (k + 1) =
            (k + 1) * (a1 + a2) + a2 * ((k + 1) * k) := by
        ring
      rw [heq]
      apply Nat.dvd_add
      · exact dvd_mul_of_dvd_right hs (k + 1)
      · obtain ⟨v, hv⟩ := Nat.two_dvd_mul_add_one k
        have hv' : (k + 1) * k = 2 * v := by
          simpa [mul_comm] using hv
        rw [hv']
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          dvd_mul_of_dvd_right h2 v

/-- Expansion of `offsetB` along an arbitrary step divisible by four. -/
private theorem offsetB_add_four_mul (p n u k : ℕ)
    (hp4 : p % 4 = 3) (hn4 : n % 4 = 1) :
    offsetB p (n + 4 * u * k) =
      offsetB p n +
        (u * (n + 4 * offsetX p n)) * k + (4 * u * u) * k * k := by
  have hfour : 4 ∣ 4 * u * k := by
    refine ⟨u * k, ?_⟩
    ring
  have hquot : (4 * u * k) / 4 = u * k := by
    simp [mul_assoc]
  rw [offsetB_add_general p n (4 * u * k) hp4 hn4 hfour, hquot]
  ring

/-- If no member of the progression `n + T*k` is divisible by a prime `p`,
then the step `T` is divisible by `p`. -/
private theorem prime_dvd_step_of_forall_not_dvd (p n T : ℕ)
    (hp : Nat.Prime p) (hnever : ∀ k : ℕ, ¬ p ∣ n + T * k) :
    p ∣ T := by
  by_contra hT
  letI : Fact p.Prime := ⟨hp⟩
  have hT0 : (T : ZMod p) ≠ 0 := by
    intro hz
    exact hT ((ZMod.natCast_eq_zero_iff T p).mp hz)
  let a : ZMod p := -(n : ZMod p) / (T : ZMod p)
  let k : ℕ := a.val
  have hk : (k : ZMod p) = a := ZMod.natCast_zmod_val a
  have hzero : ((n + T * k : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [hk]
    dsimp [a]
    field_simp
    simp
  exact hnever k ((ZMod.natCast_eq_zero_iff (n + T * k) p).mp hzero)

namespace OffsetAdmissible

/-- Characterization of all positive transport periods for one admissible seed.
The first two conditions are forced by the mod-four and nondivisibility
hypotheses.  The last two are exactly the conditions for the quadratic change
in `offsetB` to remain divisible by `d`. -/
theorem all_add_mul_iff {p d n T : ℕ} (h : OffsetAdmissible p d n)
    (hT0 : 0 < T) :
    (∀ k : ℕ, OffsetAdmissible p d (n + T * k)) ↔
      4 ∣ T ∧
      p ∣ T ∧
      d ∣ 8 * (T / 4) * (T / 4) ∧
      d ∣ (T / 4) * (n + 4 * offsetX p n + 4 * (T / 4)) := by
  rcases h with ⟨hn, hp, hp4, hn4, hpn, hd, hdb, hfirst⟩
  constructor
  · intro hall
    have h4 : 4 ∣ T := by
      apply Nat.dvd_of_mod_eq_zero
      have hnT4 := (hall 1).n_mod_four
      omega
    have hpT : p ∣ T := by
      apply prime_dvd_step_of_forall_not_dvd p n T hp
      intro k
      exact (hall k).not_p_dvd_n
    rcases h4 with ⟨u, rfl⟩
    have hpoly :
        ∀ k : ℕ,
          d ∣ (u * (n + 4 * offsetX p n)) * k + (4 * u * u) * k * k := by
      intro k
      have hnew : d ∣ offsetB p (n + 4 * u * k) :=
        (hall k).d_dvd_B
      rw [offsetB_add_four_mul p n u k hp4 hn4] at hnew
      apply (Nat.dvd_add_iff_right hdb).mpr
      convert hnew using 1
      ring
    have hcoeff :=
      (poly_dvd_all d (u * (n + 4 * offsetX p n)) (4 * u * u)).mp hpoly
    have hquot : (4 * u) / 4 = u := by omega
    refine ⟨by simp, by simpa using hpT, ?_, ?_⟩
    · simp only [hquot]
      convert hcoeff.2 using 1
      ring
    · simpa [hquot, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using hcoeff.1
  · rintro ⟨h4, hpT, hdquad, hdlin⟩
    rcases h4 with ⟨u, rfl⟩
    have hp4not : ¬ p ∣ 4 := by
      intro hp4dvd
      have hp_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) hp4dvd
      have hp_ge : 2 ≤ p := hp.two_le
      have : p = 3 := by omega
      subst p
      norm_num at hp4dvd
    have hpu : p ∣ u := by
      rcases hp.dvd_mul.mp (by simpa [mul_assoc] using hpT) with hp4dvd | hpu
      · exact (hp4not hp4dvd).elim
      · exact hpu
    have hquot : (4 * u) / 4 = u := by omega
    have hcoeff :
        d ∣ u * (n + 4 * offsetX p n) + 4 * u * u ∧
          d ∣ 2 * (4 * u * u) := by
      constructor
      · simpa [hquot, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using hdlin
      · simpa [hquot, pow_two, mul_assoc, mul_comm, mul_left_comm] using hdquad
    have hpoly :
        ∀ k : ℕ,
          d ∣ (u * (n + 4 * offsetX p n)) * k + (4 * u * u) * k * k :=
      (poly_dvd_all d (u * (n + 4 * offsetX p n)) (4 * u * u)).mpr hcoeff
    intro k
    have hshift4 : 4 ∣ 4 * u * k := by
      refine ⟨u * k, ?_⟩
      ring
    have hshiftp : p ∣ 4 * u * k := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpu 4) k
    have hdeltaP :
        p ∣ (u * (n + 4 * offsetX p n)) * k + (4 * u * u) * k * k := by
      apply Nat.dvd_add
      · simpa [mul_assoc, mul_comm, mul_left_comm] using
          dvd_mul_of_dvd_right
            (dvd_mul_of_dvd_right hpu (n + 4 * offsetX p n)) k
      · simpa [mul_assoc, mul_comm, mul_left_comm] using
          dvd_mul_of_dvd_right
            (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hpu 4) u) (k * k)
    refine ⟨by omega, hp, hp4, ?_, ?_, hd, ?_, ?_⟩
    · simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hshift4, hn4]
    · intro hnew
      exact hpn ((Nat.dvd_add_iff_left hshiftp).mpr hnew)
    · rw [offsetB_add_four_mul p n u k hp4 hn4]
      convert Nat.dvd_add hdb (hpoly k) using 1
      ring
    · rw [offsetB_add_four_mul p n u k hp4 hn4]
      convert Nat.dvd_add hfirst hdeltaP using 1
      ring

/-- The two divisor conditions in `all_add_mul_iff` force the fixed divisor to
divide the quarter-step.  Admissibility is essential here. -/
private theorem divisor_dvd_quarter_step {p d n u : ℕ}
    (h : OffsetAdmissible p d n) (hu : 0 < u)
    (hquad : d ∣ 8 * u * u)
    (hlin : d ∣ u * (n + 4 * offsetX p n + 4 * u)) :
    d ∣ u := by
  rcases h with ⟨hn, hp, hp4, hn4, hpn, hd, hdb, hfirst⟩
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hfour : 4 ∣ n + p := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  have hxrel : 4 * offsetX p n = n + p := by
    exact Nat.mul_div_cancel' hfour
  have hCrel : n + 4 * offsetX p n = 2 * n + p := by omega
  apply (Nat.factorization_le_iff_dvd hd0 hu0).mp
  intro q
  by_cases hq : Nat.Prime q
  · by_contra hle
    have hfdpos : 1 ≤ d.factorization q := by omega
    have hqd : q ∣ d :=
      (hq.dvd_iff_one_le_factorization hd0).2 hfdpos
    have hqB : q ∣ offsetB p n := hqd.trans hdb
    have hqC : ¬ q ∣ n + 4 * offsetX p n := by
      intro hqC
      have hqp : q ∣ p := by
        rcases hq.dvd_mul.mp (by simpa [offsetB] using hqB) with hqn | hqx
        · have hq2n : q ∣ 2 * n := by
            simpa [mul_comm] using dvd_mul_of_dvd_right hqn 2
          rw [hCrel] at hqC
          have hsub := Nat.dvd_sub hqC hq2n
          convert hsub using 1
          omega
        · have hq4x : q ∣ 4 * offsetX p n := by
            simpa [mul_comm] using dvd_mul_of_dvd_right hqx 4
          rw [hxrel] at hq4x
          rw [hCrel] at hqC
          have hqn0 := Nat.dvd_sub hqC hq4x
          have hqn : q ∣ n := by
            convert hqn0 using 1
            omega
          have hqp0 := Nat.dvd_sub hq4x hqn
          convert hqp0 using 1
          omega
      have hqp_eq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).1 hqp
      subst q
      exact hpn ((hp.dvd_mul.mp (by simpa [offsetB] using hqB)).resolve_right
        (by
          intro hpx
          have hp4x : p ∣ 4 * offsetX p n := by
            simpa [mul_comm] using dvd_mul_of_dvd_right hpx 4
          rw [hxrel] at hp4x
          exact hpn ((Nat.dvd_add_iff_left (dvd_refl p)).mpr hp4x)))
    have hqv : ¬ q ∣ n + 4 * offsetX p n + 4 * u := by
      by_cases hqu : q ∣ u
      · intro hqv
        have hq4u : q ∣ 4 * u := by
          simpa [mul_comm] using dvd_mul_of_dvd_right hqu 4
        exact hqC (by
          have hsub := Nat.dvd_sub hqv hq4u
          convert hsub using 1
          omega)
      · have hq8u : q ∣ 8 * u * u := hqd.trans hquad
        have hq8 : q ∣ 8 := by
          rcases hq.dvd_mul.mp hq8u with hq8u | hqu'
          · rcases hq.dvd_mul.mp hq8u with hq8 | hqu'
            · exact hq8
            · exact (hqu hqu').elim
          · exact (hqu hqu').elim
        have hqpow : q ∣ 2 ^ 3 := by simpa using hq8
        have hqeq : q = 2 :=
          Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two hqpow
        subst q
        intro h2v
        have hvmod := Nat.mod_eq_zero_of_dvd h2v
        omega
    have hpowd : q ^ d.factorization q ∣ d :=
      (hq.pow_dvd_iff_le_factorization hd0).2 le_rfl
    have hpowprod :
        q ^ d.factorization q ∣
          u * (n + 4 * offsetX p n + 4 * u) :=
      hpowd.trans hlin
    have hpowu : q ^ d.factorization q ∣ u :=
      (Nat.prime_iff.mp hq).pow_dvd_of_dvd_mul_right _ hqv hpowprod
    exact hle ((hq.pow_dvd_iff_le_factorization hu0).1 hpowu)
  · simp [Nat.factorization_eq_zero_of_not_prime, hq]

/-- Every positive transport period is a multiple of `4 * p * d`. -/
theorem period_dvd {p d n T : ℕ} (h : OffsetAdmissible p d n)
    (hT0 : 0 < T)
    (hall : ∀ k : ℕ, OffsetAdmissible p d (n + T * k)) :
    4 * p * d ∣ T := by
  have hchar := (h.all_add_mul_iff hT0).1 hall
  rcases hchar with ⟨h4, hpT, hquad, hlin⟩
  rcases h4 with ⟨u, rfl⟩
  have hu : 0 < u := by omega
  have hpu : p ∣ u := by
    rcases h with ⟨hn, hp, hp4, hn4, hpn, hd, hdb, hfirst⟩
    have hp4not : ¬ p ∣ 4 := by
      intro hp4dvd
      have hp_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) hp4dvd
      have hp_ge : 2 ≤ p := hp.two_le
      have : p = 3 := by omega
      subst p
      norm_num at hp4dvd
    rcases hp.dvd_mul.mp (by simpa [mul_assoc] using hpT) with hp4dvd | hpu
    · exact (hp4not hp4dvd).elim
    · exact hpu
  have hdu : d ∣ u := by
    apply divisor_dvd_quarter_step h hu
    · simpa using hquad
    · simpa [mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm] using hlin
  have hpd : Nat.Coprime p d := by
    rcases h with ⟨hn, hp, hp4, hn4, hpn, hd, hdb, hfirst⟩
    apply hp.coprime_iff_not_dvd.2
    intro hpd
    have hpB : p ∣ offsetB p n := hpd.trans hdb
    exact hpn ((hp.dvd_mul.mp (by simpa [offsetB] using hpB)).resolve_right
      (by
        intro hpx
        have hfour : 4 ∣ n + p := by
          apply Nat.dvd_of_mod_eq_zero
          omega
        have hxrel : 4 * offsetX p n = n + p :=
          Nat.mul_div_cancel' hfour
        have hp4x : p ∣ 4 * offsetX p n := by
          simpa [mul_comm] using dvd_mul_of_dvd_right hpx 4
        rw [hxrel] at hp4x
        exact hpn ((Nat.dvd_add_iff_left (dvd_refl p)).mpr hp4x)))
  have hpdu : p * d ∣ u :=
    hpd.mul_dvd_of_dvd_of_dvd hpu hdu
  rcases hpdu with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw [hc]
  ring

/-- A positive step preserves every transported seed exactly when it is a
multiple of `4 * p * d`. -/
theorem all_add_mul_iff_period_dvd {p d n T : ℕ}
    (h : OffsetAdmissible p d n) (hT0 : 0 < T) :
    (∀ k : ℕ, OffsetAdmissible p d (n + T * k)) ↔
      4 * p * d ∣ T := by
  constructor
  · exact h.period_dvd hT0
  · rintro ⟨c, rfl⟩ k
    simpa [mul_assoc, mul_comm, mul_left_comm] using h.add_period (c * k)

/-- The least positive transport period of every admissible seed is exactly
`4 * p * d`. -/
theorem least_positive_period {p d n : ℕ} (h : OffsetAdmissible p d n) :
    IsLeast
      {T : ℕ | 0 < T ∧ ∀ k : ℕ, OffsetAdmissible p d (n + T * k)}
      (4 * p * d) := by
  rcases h with ⟨hn, hp, hp4, hn4, hpn, hd, hdb, hfirst⟩
  have hbase : OffsetAdmissible p d n :=
    ⟨hn, hp, hp4, hn4, hpn, hd, hdb, hfirst⟩
  constructor
  · constructor
    · exact Nat.mul_pos (Nat.mul_pos (by norm_num) hp.pos) hd
    · intro k
      simpa [mul_assoc] using hbase.add_period k
  · intro T hT
    exact Nat.le_of_dvd hT.1 (hbase.period_dvd hT.1 hT.2)

end OffsetAdmissible

end ErdosStraus
