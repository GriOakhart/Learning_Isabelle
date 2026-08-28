theory Chapter_5
  imports Main

begin

section \<open>5.1 Arithmetic Expressions\<close>
subsection \<open>5.1.1 Syntax\<close>

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

term "N 5"
term "V ''y''"
term "Plus (N 5) (V ''y'')"
  \<comment> \<open>better use ''y'' rather than simply y,
      because ''y'' is a string, while y is only 'a\<close>


end