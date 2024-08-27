import CalculatingDependentlyTypedCompilers


/--
  `Ty` is an inductive type representing the types in our simple language.

  # Constructors
  * `NAT`: Represents the type of natural numbers.
  * `BOOL`: Represents the type of boolean values.

  This type is used to define the structure of expressions in the `Exp` type
  and to provide type safety in our language implementation.

  The `deriving BEq` clause automatically generates an implementation of
  boolean equality for `Ty`, allowing us to compare `Ty` values using `==`.
-/
inductive Ty where
  | NAT
  | BOOL
deriving BEq, Repr

/--
  `asType` is an abbreviation that maps a `Ty` to its corresponding Lean type.

  # Cases
  * For `Ty.NAT`, it returns `Nat` (natural numbers).
  * For `Ty.BOOL`, it returns `Bool` (boolean values).

  This function is used to interpret the abstract syntax types (`Ty`) as concrete Lean types,
  which is crucial for defining and working with expressions (`Exp`) in a type-safe manner.
-/
abbrev asType : (T : Ty) → Type
| .NAT => Nat
| .BOOL => Bool

/--
  The `Exp` type represents expressions in a simple language with natural numbers and booleans.
  It is parameterized by a `Ty` which determines the type of the expression.

  # Constructors
  * `val`: Represents a literal value of the given type.
  * `add`: Represents addition of two natural number expressions.
  * `ite`: Represents an if-then-else expression, where the condition is a boolean expression.
-/
inductive Exp : Ty → Type where
  /-- Constructs a literal value of the given type. -/
  | val : asType T → Exp T
  /-- Constructs an addition expression for natural numbers. -/
  | add : Exp .NAT → Exp .NAT → Exp .NAT
  /-- Constructs an if-then-else expression. -/
  | ite : Exp .BOOL → Exp T → Exp T → Exp T


/--
  The `eval` function evaluates an expression of type `Exp T` to a value of type `asType T`.

  # Parameters
  * `T : Ty` - The type of the expression (inferred from context)

  # Returns
  * `asType T` - The evaluated result of the expression

  # Cases
  * For `val x`, it returns the literal value `x`.
  * For `add e1 e2`, it recursively evaluates `e1` and `e2` and returns their sum.
  * For `ite e1 e2 e3`, it evaluates the condition `e1` and then evaluates and returns either `e2` or `e3` based on the condition.

  # Note
  This function assumes that the `+` operator is defined for `asType Ty.NAT`,
  and that boolean evaluation is possible for `asType Ty.BOOL`.
-/
def eval : Exp T → asType T
| .val x => x
| .add e1 e2 => eval e1 + eval e2
| .ite e1 e2 e3 => if eval e1 then eval e2 else eval e3

/--
  The `Stack` type represents a stack of values, where each value has a type from the `Ty` enumeration.
  It is parameterized by a list of `Ty`, which represents the types of the values in the stack.

  # Constructors
  * `empty`: Represents an empty stack.
  * `push`: Adds a new value to the top of the stack.

  # Type Parameters
  * `List Ty`: A list of types representing the structure of the stack.

  # Usage
  This inductive type is crucial for modeling the state of a stack machine,
  which is often used in compiler implementations and formal semantics of programming languages.
-/
inductive Stack : List Ty → Type where
  /-- Constructs an empty stack. -/
  | empty : Stack []
  /-- Pushes a value of type `asType ty` onto a stack of type `Stack tys`, resulting in a new stack of type `Stack (ty :: tys)`. -/
  | push {ty : Ty} : asType ty → Stack tys → Stack (ty :: tys)
deriving Repr

/--
  Defines infix notation for Stack operations.

  # Operators
  * `ε`: Represents an empty stack. It is an infix operator with precedence 60.
  * `▹`: Represents the push operation. It is an infix operator with precedence 60.

  # Usage
  * `ε` can be used to create an empty stack: `Stack.empty` becomes `ε`
  * `▹` can be used to push elements onto a stack: `Stack.push x s` becomes `x ▹ s`

  # Precedence
  Both operators have a precedence of 60, which means they bind more tightly than most arithmetic operations but less tightly than function application.

  # Examples
  * Creating an empty stack: `ε`
  * Pushing a value onto a stack: `5 ▹ ε`
  * Pushing multiple values: `1 ▹ 2 ▹ 3 ▹ ε`
-/
notation "ε" => Stack.empty
infix:60 "▹" => Stack.push

/--
  The `Code` inductive type represents instructions for a stack machine.
  It is parameterized by two lists of `Ty`, representing the initial and final stack types.

  # Constructors
  * `PUSH`: Pushes a value onto the stack.
  * `ADD`: Adds the top two numbers on the stack.
  * `IF`: Conditional branching based on a boolean value.
  * `HALT`: Terminates the program.

  # Type Parameters
  * `List Ty → List Ty → Type`: The first list represents the initial stack types,
    and the second list represents the final stack types after executing the code.

  # Usage
  This type is used to represent compiled expressions and is crucial for
  the implementation of a type-safe stack machine.
-/
inductive Code : List Ty → List Ty → Type where
  /-- Pushes a value of type `asType ty` onto the stack. -/
  | PUSH {ty : Ty} : asType ty → Code (ty :: tys) tys' → Code tys tys'
  /-- Adds the top two natural numbers on the stack. -/
  | ADD {tys : List Ty} : Code (.NAT :: tys) tys' → Code (.NAT :: .NAT :: tys) tys'
  /-- Conditional branching based on a boolean value at the top of the stack. -/
  | IF : Code tys tys' → Code tys tys' → Code (.BOOL :: tys) tys'
  /-- Terminates the program, leaving the stack unchanged. -/
  | HALT : Code tys tys



/--
  Compiles an expression of type `Exp ty` into a sequence of `Code` instructions.

  # Parameters
  * `e : Exp ty`: The expression to compile.

  # Returns
  * `Code tys (ty :: tys)`: A sequence of `Code` instructions that, when executed,
    will evaluate the expression and push the result onto the stack.

  # Implementation
  The compilation is done using a helper function `doComp` which recursively
  compiles the expression and appends the resulting code to a continuation.

  # Helper function: doComp
  `doComp` takes an expression and a continuation, and returns the code that
  evaluates the expression and then executes the continuation.

  ## Parameters
  * `{ty : Ty}`: The type of the expression being compiled.
  * `{tys tys' : List Ty}`: The initial and final stack types.
  * `Exp ty`: The expression to compile.
  * `Code (ty :: tys) tys'`: The continuation code.

  ## Returns
  * `Code tys tys'`: The compiled code for the expression followed by the continuation.

  ## Cases
  * For a value (.val x), it pushes the value onto the stack.
  * For addition (.add x y), it recursively compiles x and y, then adds the results.
  * For if-then-else (.ite b t e), it compiles the condition, then uses IF to branch
    between the compiled 'then' and 'else' expressions.
-/
def compile (e : Exp ty) : Code tys (ty :: tys) :=
  doComp e .HALT
where
  doComp {ty : Ty} {tys tys' : List Ty} : Exp ty → Code (ty :: tys) tys' → Code tys tys'
  | .val x, c => .PUSH x c
  | .add x y, c => doComp x <| doComp y <| .ADD c
  | .ite b t e, c => doComp b <| .IF (doComp t c) (doComp e c)

def exec : Code tys tys' → Stack tys → Stack tys'
| .PUSH x c, s => exec c (x ▹ s)
| .ADD c, (m ▹ (n ▹ s)) => exec c ((m + n) ▹ s)
| .IF t e, (b ▹ s) => if b then exec t s else exec e s
| .HALT, s => s


/--
  Correctness theorem for the compiler.

  This theorem states that executing the compiled code of an expression
  is equivalent to evaluating the expression and pushing the result onto the stack.

  # Statement
  For any expression `e` of type `Exp ty` and any initial stack `s`,
  executing the compiled code of `e` on `s` is the same as
  evaluating `e` and pushing the result onto `s`.

  # Parameters
  * `e : Exp ty`: The expression being compiled and evaluated.
  * `s : Stack tys`: The initial stack.

  # Proof
  The proof is not provided here (marked as `sorry`).
  It would typically be done by induction on the structure of `e`,
  considering each case of the `Exp` datatype.

  # Note
  This theorem establishes the semantic correctness of our compiler,
  ensuring that the compilation preserves the meaning of expressions.
-/
theorem correct : exec (compile e) s = eval e ▹ s := sorry



def main : IO Unit := do
  let x : Exp .NAT := .val 5
  let y : Exp .NAT := .val 7
  let z : Exp .NAT := .add x y
  let c : Code [] [.NAT] := compile z
  let s : Stack [] := ε
  let s' : Stack [.NAT] := exec c s
  IO.println s!"Hello!"
