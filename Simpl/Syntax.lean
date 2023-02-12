import Lean

namespace Simpl

declare_syntax_cat statement
declare_syntax_cat expression

syntax "SKIP" : statement
syntax ident ":==" expression : statement
syntax statement ";" statement : statement
syntax "IF" expression "THEN" statement "ELSE" statement "FI" : statement
syntax "WHILE" expression "DO" statement "OD" : statement
syntax "TRY" statement "CATCH" statement "END" : statement
syntax "THROW" expression : statement
syntax "Call" ident : statement
syntax "Guard" expression expression statement : statement

syntax num : expression
syntax ident : expression
syntax expression "+" expression : expression
syntax expression "-" expression : expression
syntax "(" expression ")" : expression

-- can we build this automatically from the above? (at least without the parentheses)
mutual
inductive Statement where
  | skip : Statement
  | assign : Lean.Name → Expression → Statement
  | seq : Statement → Statement → Statement
  | conditional : Expression → Statement → Statement → Statement
  | while : Expression → Statement → Statement
  | trycatch : Statement → Statement → Statement
  | throw : Expression → Statement
  | call : Lean.Name → Statement
  | guard : Expression → Expression → Statement → Statement
  deriving Inhabited, Repr

 inductive Expression where
  | num : Nat → Expression
  | ident : Lean.Name → Expression
  | add : Expression → Expression → Expression
  | sub : Expression → Expression → Expression
  deriving Inhabited, Repr
end

syntax "[simpl_expr|" expression "]" : term
syntax "[simpl|" statement "]" : term

macro_rules
  | `([simpl| SKIP]) => `(Statement.skip)
  | `([simpl| $i:ident :== $e]) => `(Statement.assign $(Lean.quote i.getId) [simpl_expr| $e])
  | `([simpl| $s1; $s2]) => `(Statement.seq [simpl| $s1] [simpl| $s2])
  | `([simpl| IF $e THEN $s1 ELSE $s2 FI]) => `(Statement.conditional [simpl_expr| $e] [simpl| $s1] [simpl| $s2])
  | `([simpl| WHILE $e DO $s OD]) => `(Statement.while [simpl_expr| $e] [simpl| $s])
  | `([simpl| TRY $s1 CATCH $s2 END]) => `(Statement.trycatch [simpl| $s1] [simpl| $s2])
  | `([simpl| THROW $e]) => `(Statement.throw [simpl_expr| $e])
  | `([simpl| Call $i]) => `(Statement.call $(Lean.quote i.getId))
  | `([simpl| Guard $e1 $e2 $s]) => `(Statement.guard [simpl_expr| $e1] [simpl_expr| $e2] [simpl| $s])

macro_rules
  | `([simpl_expr| $n:num]) => `(Expression.num $n)
  | `([simpl_expr| $i:ident]) => `(Expression.ident $(Lean.quote i.getId))
  | `([simpl_expr| $e1 + $e2]) => `(Expression.add [simpl_expr| $e1] [simpl_expr| $e2])
  | `([simpl_expr| $e1 - $e2]) => `(Expression.sub [simpl_expr| $e1] [simpl_expr| $e2])

end Simpl
