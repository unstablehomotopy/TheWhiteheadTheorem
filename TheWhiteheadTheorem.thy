theory Example
  imports Main
begin

(* Define a simple function to add two natural numbers *)
fun add :: "nat ⇒ nat ⇒ nat" where
  "add 0 m = m" |
  "add (Suc n) m = Suc (add n m)"

(* Prove that addition is commutative *)
theorem add_commutative: "add n m = add m n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

end