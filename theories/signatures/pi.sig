-- I can add a preamble with -p to autosubst!!
-- If something doesn't work: try adding scons_eta' from unscoped.v to asimpl
-- Note: in π calculus Channels are Values (so there is just one type)

proc  : Type
Data : Type

Value : Type
Equation : Type

cst : Value -> Data

tt : Equation
ff : Equation
Inequality : Data -> Data -> Equation
Or : Equation -> Equation -> Equation
Not : Equation -> Equation

pr_success : proc
pr_nil : proc
pr_rec : (bind proc in proc) -> proc
pr_choice : proc -> proc -> proc
pr_par : proc -> proc -> proc
pr_output : Data  -> Data -> proc -> proc
pr_res : (bind Data in proc) -> proc
pr_input : Data -> (bind Data in proc) -> proc
-- pr_res : (bind Data in proc) -> proc
-- pr_input : Data -> (bind Data in proc) -> proc
pr_tau : proc -> proc
pr_if_then_else : Equation -> proc -> proc -> proc