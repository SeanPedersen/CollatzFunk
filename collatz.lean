/-
Collatz conjecture

To prove it you just need to replace
sorry below by a proof.
-/

set_option pp.structure_projections false

inductive step : ℕ → ℕ → Prop 
| even : ∀ n : ℕ , step (2 * n) n
| odd : ∀ n : ℕ , step (2 * n + 1) (6 * n + 4)

open step

inductive collatz : ℕ → Prop 
| one : collatz 1
| go : ∀ m n : ℕ , 
    step m n → collatz n → collatz m 

-- collatz n means that the Collatz sequence
-- starting with n terminates.

open collatz

open nat

def exp2 : ℕ → ℕ 
| 0 := 1
| (succ n) := 2*(exp2 n)

lemma power : ∀ n : ℕ, collatz (exp2 n) :=
begin 
  assume n,
  induction n with n' ih,
  apply one,
  apply (go (exp2 (succ n')) (exp2 n')),
  apply (even (exp2 n')),
  exact ih,
end

-- example: the collatz sequence 
-- starting with 10 terminates.
example : collatz 10 :=
begin
  apply (go 10 5),
  apply (even 5),
  apply (go 5 16),
  apply (odd 2),
  apply (power 4),
end

-- to do: show that collatz terminates
-- for all natural numbers.
theorem famous : ∀ n : ℕ, collatz n :=
begin
  sorry,
end