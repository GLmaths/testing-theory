-- I can add a preamble with -p to autosubst!!
-- If something doesn't work: try adding scons_eta' from unscoped.v to asimpl
-- Note: in π calculus Channels are Values (so there is just one type)

proc  : Type
gproc : Type
Data  : Type

Value : Type
Equation : Type

cst : Value -> Data

tt : Equation
ff : Equation
Inequality : Data -> Data -> Equation
Or : Equation -> Equation -> Equation
Not : Equation -> Equation

pr_rec : (bind proc in proc) -> proc
pr_par : proc -> proc -> proc
pr_res : (bind Data in proc) -> proc
pr_if_then_else : Equation -> proc -> proc -> proc
g : gproc -> proc

gpr_success : gproc
gpr_nil : gproc
-- note that output was not a guard in CCS
gpr_output : Data  -> Data -> proc -> gproc
gpr_input : Data -> (bind Data in proc) -> gproc
gpr_tau : proc -> gproc
gpr_choice : gproc -> gproc -> gproc
