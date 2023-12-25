import «Pfmt»

open Pfmt

def assertEq (lhs rhs : String) : IO Bool := do
  if lhs == rhs then
    return true
  else
    IO.println s!"Strings are not equal:\nLeft:\n{lhs}\nRight:\n{rhs}"
    return false

def printDocChoice (w : Nat) : String :=
  let exit_d := .text "exit();"
  let d :=
    .text "while (true) {" ++
      .nest 4
        (.newline ++ .text "f();" ++ .newline ++ .text "if (done())" ++
             (.choice
               (.space ++ exit_d)
               (.nest 4 (.newline ++ exit_d)))
             ) ++
      .newline ++ .text "}"
  Doc.prettyPrint (χ := DefaultCost) d 0 w

def test_choice_doc_80 : IO Bool :=
  assertEq
    (String.intercalate "\n"
       [ "while (true) {"
       , "    f();"
       , "    if (done()) exit();"
       , "}"
       ])
    (printDocChoice 80)

def test_choice_doc_20 : IO Bool :=
  assertEq
    (String.intercalate "\n"
       [ "while (true) {"
       , "    f();"
       , "    if (done())"
       , "        exit();"
       , "}"
       ])
    (printDocChoice 20)

def runTests (tests : List (String × IO Bool)) : IO Bool := do
  for (name, test) in tests do
    if ← test then
      IO.println s!"{name}: SUCCESS"
    else
      IO.println s!"{name}: FAILURE"
      return false
  return true

def main : IO UInt32 := do
  let ret ← runTests [
    ("choice 80", test_choice_doc_80),
    ("choice 20", test_choice_doc_20),
  ]
  if ret then
    return 0
  else
    return 1
