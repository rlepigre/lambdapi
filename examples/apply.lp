symbol const A : TYPE
symbol const B : TYPE

theorem test1 : (A ⇒ B) ⇒ A ⇒ B
proof
  intro h1 h2
  apply h1
  apply h2
qed

symbol const C : TYPE

theorem test2 : (A ⇒ B ⇒ C) ⇒ A ⇒ B ⇒ C
proof
  intro h1 h2 h3
  apply h1
  apply h2
  apply h3
qed
