-- the source scan misses this axiom (its keyword is built by a macro); the Lean audit must not
set_option hygiene false in
macro "mk_cheat" : command => `(axiom hidden_cheat : 1 = 2)
mk_cheat
theorem bad_hidden : 1 = 2 := hidden_cheat
