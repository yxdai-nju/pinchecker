%---------------------------------------------------------------------------%
%
% File: pinchecker.m
% Version: 0.1.2
% Author: Yuxuan Dai <yxdai@smail.nju.edu.cn>
%
% This module provides an compilable implementation of PinChecker.
%
%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%

:- module pinchecker.
:- interface.

:- import_module list.

%---------------------------------------------------------------------------%

    % Represents a Rust-style statement
    %
:- type rs_stmt(Func)
    --->    rs_stmt(
                int,        % line number
                Func,       % function called
                list(int)   % arguments (variable indices)
            )
    ;       rs_stmt_free(
                int         % line number
            ).

    % Defines RPIL (Reference Provenance Intermediate Language) operators
    %
:- type rpil_op
    --->    arg(int)
    ;       var(int)
    ;       place(rpil_op, int)
    ;       place_ext(rpil_op)
    ;       variant_place(rpil_op, int, int)
    ;       deref(rpil_op).

    % Defines RPIL instructions
    %
:- type rpil_inst
    --->    rpil_bind(rpil_op, rpil_op)
    ;       rpil_move(rpil_op)
    ;       rpil_borrow(rpil_op, rpil_op)
    ;       rpil_borrow_mut(rpil_op, rpil_op)
    ;       rpil_deref_move(rpil_op)
    ;       rpil_deref_pin(rpil_op).

    % Defines types of borrowing in Rust
    %
:- type borrow_kind
    --->    shared
    ;       mutable.

    % Defines liveness states of a variable in Rust
    %
:- type liveness_state
    --->    alive
    ;       dead.

    % Defines pinning states of a place in Rust
    %
:- type pinning_state
    --->    pinned
    ;       moved.

    % Typeclass for Rust functions, types and trait implementations
    %
:- typeclass rust_tc(Func, Type, Trait) <= (
    showable(Func), % required in `show_rs_stmt'
    (Func -> Type),
    (Type -> Func, Trait)
) where [
        % Returns the RPIL instructions for a given function
        %
    func fn_rpil_tcm(Func) = list(rpil_inst),

        % Checks if a function preserves its arguments' liveness states after
        % being called (e.g., borrow/borrow_mut)
        %
    pred does_not_kill_arguments_tcm(Func),
    mode does_not_kill_arguments_tcm(in) is semidet,

        % Determines function return type by providing argument types, or
        % list all possible "function - argument types" pairs, by providing
        % the return type
        %
    pred fn_typing_tcm(Func, list(Type), Type),
    mode fn_typing_tcm(in, in, out) is nondet,
    mode fn_typing_tcm(out, out, in) is multi,

        % Checks if a type lives even after being killed (e.g., shared
        % references, types that implement `Copy' trait)
        %
    pred lives_even_after_killing_tcm(Type),
    mode lives_even_after_killing_tcm(in) is semidet,

        % Checks if a type implements a trait
        %
    pred impl_trait_tcm(Type, Trait),
    mode impl_trait_tcm(in, out) is nondet
].

    % Typeclass for string representations
    %
:- typeclass showable(T) where [
    func show(T) = string
].

%---------------------%
%
% Core generation logic
%

    % Creates a list of free statements
    %
:- func free_stmts(int) = list(rs_stmt(Func)) <= rust_tc(Func, Type, Trait).

    % Generates statements by applying typing constraints
    %
:- pred ctx_typing_gen(list(rs_stmt(Func)), list(rs_stmt(Func)), int, Type) <= rust_tc(Func, Type, Trait).
:- mode ctx_typing_gen(in, out, in, in) is nondet.

%---------------------%
%
% Typing/liveness/borrowing context
%

    % Checks/retrieves the type of a variable
    %
:- pred ctx_typing(list(rs_stmt(Func)), int, Type) <= rust_tc(Func, Type, Trait).
:- mode ctx_typing(in, in, out) is nondet.

    % Checks/retrieves the liveness state of a variable
    %
:- pred ctx_liveness(list(rs_stmt(Func)), int, liveness_state) <= rust_tc(Func, Type, Trait).
:- mode ctx_liveness(in, in, out) is semidet.

    % Checks/retrieves borrowing relationships between RPIL operators (get
    % RHS and borrow kind, by providing LHS)
    %
:- pred ctx_borrowing(list(rs_stmt(Func)), rpil_op, rpil_op, borrow_kind) <= rust_tc(Func, Type, Trait).
:- mode ctx_borrowing(in, in, out, out) is semidet.

    % TODO: doc
    %
:- pred ctx_pinning(list(rs_stmt(Func)), rpil_op, pinning_state) <= rust_tc(Func, Type, Trait).
:- mode ctx_pinning(in, in, out) is semidet.

%---------------------%
%
% Display utilities
%

:- func show_rs_stmt(rs_stmt(Func)) = string <= showable(Func).

:- func show_rs_stmts(list(rs_stmt(Func))) = string <= showable(Func).

:- func show_rpil_op(rpil_op) = string.

%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%

:- implementation.

:- import_module int.
:- import_module require.
:- import_module string.

%---------------------------------------------------------------------------%

%---------------------%
%
% Performs RPIL reduction
%

    % Reduces the RPIL instructions for a given function
    %
:- func fn_rpil_reduced(Func, list(int)) = list(rpil_inst) <= rust_tc(Func, Type, Trait).

    % Reduces a list of RPIL instructions
    %
:- func rpil_reduction(list(int), list(rpil_inst)) = list(rpil_inst).

    % Reduces a single RPIL instruction
    %
:- func rpil_inst_reduction(list(int), rpil_inst) = rpil_inst.

    % Reduces a term in an RPIL instruction
    %
:- func rpil_term_reduction(list(int), rpil_op) = rpil_op.

%---------------------%
%
% Relevant to the typing/borrowing/pinning context
%

    % Applies typing constraints to pairs of variables and types
    %
:- pred ctx_typing_gen_chain(list(rs_stmt(Func)), list(rs_stmt(Func)), list(int), list(Type)) <= rust_tc(Func, Type, Trait).
:- mode ctx_typing_gen_chain(in, out, in, in) is nondet.

    % Finds a variable that could possibly be of a certain type
    %
:- pred ctx_typing_findvar(list(rs_stmt(Func)), Type, int) <= rust_tc(Func, Type, Trait).
:- mode ctx_typing_findvar(in, in, out) is nondet.

    % Checks borrowing relationships between RPIL places, by providing not
    % only statements, but also partially interpreted RPIL instructions of
    % the next statement
    %
:- pred ctx_borrowing_partial(list(rs_stmt(Func)), list(rpil_inst), rpil_op, rpil_op, borrow_kind) <= rust_tc(Func, Type, Trait).
:- mode ctx_borrowing_partial(in, in, in, out, out) is semidet.

    % TODO: doc
    %
:- pred ctx_pinning_partial(list(rs_stmt(Func)), list(rpil_inst), rpil_op, pinning_state) <= rust_tc(Func, Type, Trait).
:- mode ctx_pinning_partial(in, in, in, out) is semidet.

%---------------------%
%
% Relevant to RPIL operators
%

    % Interprets the RPIL `deref(_)' operator by following through borrows in
    % the borrowing context
    %
:- pred follow_deref(list(rs_stmt(Func)), list(rpil_inst), rpil_op, rpil_op) <= rust_tc(Func, Type, Trait).
:- mode follow_deref(in, in, in, out) is semidet.

    % Gets the origin (variable index) of an RPIL operator
    %
:- func origin(rpil_op) = int.

    % TODO: doc
    %
:- pred contagious_origin(rpil_op, rpil_op).
:- mode contagious_origin(in, out) is semidet.

    % Replaces the origin of an RPIL operator
    %
:- pred replace_origin(rpil_op, rpil_op, rpil_op, rpil_op).
:- mode replace_origin(in, in, in, out) is semidet.

%---------------------%
%
% Display utilities
%

:- func show_rpil_inst(rpil_inst) = string.

:- func show_rpil_insts(list(rpil_inst)) = string.

:- func show_liveness(liveness_state) = string.

:- func show_borrow_kind(borrow_kind) = string.

%---------------------------------------------------------------------------%

free_stmts(L) = Stmts :-
    ( L > 0 ->
        Stmt = rs_stmt_free(L),
        Stmts = [Stmt | free_stmts(L - 1)]
    ; L = 0 ->
        Stmts = []
    ;
        unexpected($pred, "invalid length")
    ).

ctx_typing_gen(Stmts_in, Stmts_out, Var, Type) :-
    Stmts_in = [Stmt_in | StmtsR_in],
    Stmt_in = rs_stmt_free(L),
    ( Var = L ->
        fn_typing_tcm(Fn, ArgTypes, Type),
        list.map(ctx_typing_findvar(StmtsR_in), ArgTypes, Args),
        Stmt_out = rs_stmt(L, Fn, Args),
        ctx_typing_gen_chain(StmtsR_in, StmtsR_out, Args, ArgTypes),
        list.all_true(
            (pred(Arg::in) is semidet :-
                ctx_liveness(StmtsR_out, Arg, alive)
            ),
            Args
        ),
        Stmts_out = [Stmt_out | StmtsR_out]
    ;
        ctx_typing_gen(StmtsR_in, StmtsR_out, Var, Type),
        Stmts_out = [Stmt_in | StmtsR_out]
    ).
ctx_typing_gen(Stmts_in, Stmts_out, Var, Type) :-
    Stmts_in = [Stmt_in | StmtsR_in],
    Stmt_in = rs_stmt(L, _Fn, _Args),
    ( Var = L ->
        ctx_typing(Stmts_in, Var, Type),
        Stmts_out = [Stmt_in | StmtsR_in]
    ;
        ctx_typing_gen(StmtsR_in, StmtsR_out, Var, Type),
        Stmts_out = [Stmt_in | StmtsR_out]
    ).

ctx_typing_gen_chain(In, Out, [], []) :- 
    Out = In.
ctx_typing_gen_chain(In, Out, [Var | VarsR], [Type | TypesR]) :-
    ctx_typing_gen(In, Mid, Var, Type),
    ctx_typing_gen_chain(Mid, Out, VarsR, TypesR).

ctx_typing_findvar(Stmts, Type, Var) :-
    Stmts = [Stmt | StmtsR],
    (
        (
            Stmt = rs_stmt(L, Fn, Args),
            fn_typing_tcm(Fn, ArgTypes, Type),
            list.map(ctx_typing(StmtsR), Args, ArgTypes)
        ;
            Stmt = rs_stmt_free(L)
        ),
        Var = L
    ;
        ctx_typing_findvar(StmtsR, Type, Var)
    ).

%---------------------%

fn_rpil_reduced(Fn, Ops) = RpilReduced :-
    Rpil = fn_rpil_tcm(Fn),
    RpilReduced = rpil_reduction(Ops, Rpil).

rpil_reduction(Ops, Rpil) = RpilReduced :-
    RpilReduced = list.map(rpil_inst_reduction(Ops), Rpil).

rpil_inst_reduction(Ops, rpil_bind(Term1, Term2)) =
    rpil_bind(TermR1, TermR2) :-
    TermR1 = rpil_term_reduction(Ops, Term1),
    TermR2 = rpil_term_reduction(Ops, Term2).
rpil_inst_reduction(Ops, rpil_move(Term)) =
    rpil_move(TermR) :-
    TermR = rpil_term_reduction(Ops, Term).
rpil_inst_reduction(Ops, rpil_borrow(Term1, Term2)) =
    rpil_borrow(TermR1, TermR2) :-
    TermR1 = rpil_term_reduction(Ops, Term1),
    TermR2 = rpil_term_reduction(Ops, Term2).
rpil_inst_reduction(Ops, rpil_borrow_mut(Term1, Term2)) =
    rpil_borrow_mut(TermR1, TermR2) :-
    TermR1 = rpil_term_reduction(Ops, Term1),
    TermR2 = rpil_term_reduction(Ops, Term2).
rpil_inst_reduction(Ops, rpil_deref_move(Term)) =
    rpil_deref_move(TermR) :-
    TermR = rpil_term_reduction(Ops, Term).
rpil_inst_reduction(Ops, rpil_deref_pin(Term)) =
    rpil_deref_pin(TermR) :-
    TermR = rpil_term_reduction(Ops, Term).

rpil_term_reduction(Ops, arg(Idx)) = TermR :-
    ( list.index0(Ops, Idx, Var) ->
        TermR = var(Var)
    ;
        unexpected($pred, "invalid index")
    ).
rpil_term_reduction(_, var(_)) =
    unexpected($pred, "cannot reduce a reduced RPIL operator").
rpil_term_reduction(Ops, place(Term, P)) =
    place(TermR, P) :-
    TermR = rpil_term_reduction(Ops, Term).
rpil_term_reduction(Ops, place_ext(Term)) =
    place_ext(TermR) :-
    TermR = rpil_term_reduction(Ops, Term).
rpil_term_reduction(Ops, variant_place(Term, V, P)) =
    variant_place(TermR, V, P) :-
    TermR = rpil_term_reduction(Ops, Term).
rpil_term_reduction(Ops, deref(Term)) =
    deref(TermR) :-
    TermR = rpil_term_reduction(Ops, Term).

%---------------------%

ctx_typing([Stmt | StmtsR], Var, Type) :-
    Stmt = rs_stmt(L, Fn, Args),
    ( Var = L ->
        list.map(ctx_typing(StmtsR), Args, ArgTypes),
        fn_typing_tcm(Fn, ArgTypes, Type)
    ;
        ctx_typing(StmtsR, Var, Type)
    ).
ctx_typing([Stmt | StmtsR], Var, Type) :-
    Stmt = rs_stmt_free(L),
    ( Var = L ->
        false
    ;
        ctx_typing(StmtsR, Var, Type)
    ).

%---------------------%

ctx_liveness([Stmt | _], _, Liveness) :-
    Stmt = rs_stmt_free(_L),
    Liveness = alive.
ctx_liveness([Stmt | StmtsR], Var, Liveness) :-
    Stmt = rs_stmt(L, Fn, Args),
    ( Var = L ->
        Liveness = alive
    ; list.member(Var, Args) ->
        ctx_liveness(StmtsR, Var, alive),
        ( does_not_kill_arguments_tcm(Fn) ->
            Liveness = alive
        ; ctx_typing(StmtsR, Var, VarType),
          lives_even_after_killing_tcm(VarType) ->
            Liveness = alive
        ;
            Liveness = dead
        )
    ;
        ctx_liveness(StmtsR, Var, Liveness)
    ).

%---------------------%

ctx_borrowing(Stmts, Lhs, Rhs, Kind) :-
    Stmts = [Stmt | StmtsR],
    Stmt = rs_stmt(L, Fn, Args),
    RpilInsts = fn_rpil_reduced(Fn, [L | Args]),
    ctx_borrowing_partial(StmtsR, RpilInsts, Lhs, Rhs, Kind),
    ctx_liveness(Stmts, origin(Lhs), alive),
    ctx_liveness(Stmts, origin(Rhs), alive).
ctx_borrowing(Stmts, Lhs, Rhs, Kind) :-
    Stmts = [Stmt | StmtsR],
    Stmt = rs_stmt_free(_L),
    ctx_borrowing(StmtsR, Lhs, Rhs, Kind).

ctx_borrowing_partial(Stmts, [], Lhs, Rhs, Kind) :-
    ctx_borrowing(Stmts, Lhs, Rhs, Kind).
ctx_borrowing_partial(Stmts, Insts, Lhs, Rhs, Kind) :-
    Insts = [Inst | InstsR],
    ( Inst = rpil_borrow(OpL, OpR),
      follow_deref(Stmts, Insts, OpL, Lhs) ->
        follow_deref(Stmts, Insts, OpR, Rhs),
        Kind = shared
    ; Inst = rpil_borrow_mut(OpL, OpR),
      follow_deref(Stmts, Insts, OpL, Lhs) ->
        follow_deref(Stmts, Insts, OpR, Rhs),
        Kind = mutable
    ; Inst = rpil_bind(OpL, OpR),
      follow_deref(Stmts, Insts, OpL, OpLFD),
      follow_deref(Stmts, Insts, OpR, OpRFD),
      replace_origin(Lhs, OpLFD, OpRFD, Bound) ->
        ctx_borrowing_partial(Stmts, InstsR, Bound, Rhs, Kind)
    ;
        ctx_borrowing_partial(Stmts, InstsR, Lhs, Rhs, Kind)
    ).

%---------------------%

ctx_pinning(Stmts, Place, Status) :-
    Stmts = [Stmt | StmtsR],
    Stmt = rs_stmt(L, Fn, Args),
    RpilInsts = fn_rpil_reduced(Fn, [L | Args]),
    ctx_pinning_partial(StmtsR, RpilInsts, Place, Status).
ctx_pinning(Stmts, Place, Status) :-
    Stmts = [Stmt | StmtsR],
    Stmt = rs_stmt_free(_L),
    ctx_pinning(StmtsR, Place, Status).

ctx_pinning_partial(Stmts, [], Place, Status) :-
    ctx_pinning(Stmts, Place, Status).
ctx_pinning_partial(Stmts, Insts, Place, Status) :-
    Insts = [Inst | InstsR],
    ( ctx_pinning_partial(Stmts, InstsR, Place, StatusR) ->
        (
            StatusR = pinned,
            ( Inst = rpil_deref_move(BrwConPlace),
              ctx_borrowing_partial(Stmts, InstsR, BrwConPlace, ConPlace, _Kind),
              contagious_origin(Place, ConPlace) ->
                Status = moved
            ; Inst = rpil_move(ConPlace),
              contagious_origin(Place, ConPlace) ->
                Status = moved
            ;
                Status = pinned
            )
        ;
            StatusR = moved,
            Status = moved
        )
    ;
        Inst = rpil_deref_pin(BrwPlace),
        ctx_borrowing_partial(Stmts, InstsR, BrwPlace, Place, _Kind),
        Status = pinned
    ).

%---------------------%

follow_deref(Stmts, Insts, Op0, Op) :-
    (
        Op0 = arg(_),
        unexpected($pred, "cannot follow dereferences before RPIL reduction")
    ;
        Op0 = var(_),
        Op = Op0
    ;
        Op0 = place(Op1, P),
        follow_deref(Stmts, Insts, Op1, Op2),
        Op = place(Op2, P)
    ;
        Op0 = place_ext(Op1),
        follow_deref(Stmts, Insts, Op1, Op2),
        Op = place_ext(Op2)
    ;
        Op0 = variant_place(Op1, V, P),
        follow_deref(Stmts, Insts, Op1, Op2),
        Op = variant_place(Op2, V, P)
    ;
        Op0 = deref(Op1),
        follow_deref(Stmts, Insts, Op1, Op2),
        ctx_borrowing_partial(Stmts, Insts, Op2, Op, _Kind)
    ).

origin(arg(_)) =
    unexpected($pred, "cannot determine origin before RPIL reduction").
origin(var(X)) = X.
origin(place(X0, _)) = origin(X0).
origin(place_ext(X0)) = origin(X0).
origin(variant_place(X0, _, _)) = origin(X0).
origin(deref(X0)) = origin(X0).

contagious_origin(var(X), var(X)).
contagious_origin(place(X0, _), X) :-
    contagious_origin(X0, X).
contagious_origin(variant_place(X0, _, _), X) :-
    contagious_origin(X0, X).

replace_origin(X0, X, Y, Y0) :-
    ( X = X0 ->
        Y0 = Y
    ;
        (
            X0 = place(X1, P),
            replace_origin(X1, X, Y, Y1),
            Y0 = place(Y1, P)
        ;
            X0 = place_ext(X1),
            replace_origin(X1, X, Y, Y1),
            Y0 = place_ext(Y1)
        ;
            X0 = variant_place(X1, V, P),
            replace_origin(X1, X, Y, Y1),
            Y0 = variant_place(Y1, V, P)
        ;
            X0 = deref(X1),
            replace_origin(X1, X, Y, Y1),
            Y0 = deref(Y1)
        )
    ).

%---------------------%

show_rs_stmt(rs_stmt(Line, Fn, Args)) = Repr :-
    FnRepr = show(Fn),
    ArgStrs = list.map(
        (func(Arg) = string.format("v%d", [i(Arg)])),
        Args),
    ArgsRepr = string.join_list(", ", ArgStrs),
    Repr = string.format(
        "let v%d = %s(%s);",
        [i(Line), s(FnRepr), s(ArgsRepr)]).
show_rs_stmt(rs_stmt_free(Line)) =
    string.format("let v%d = ..;", [i(Line)]).

show_rs_stmts(Stmts) = string.join_list("\n", Reprs) :-
    RevReprs = list.map(show_rs_stmt, Stmts),
    Reprs = list.reverse(RevReprs).

show_rpil_op(arg(N)) =
    string.format("_%d", [i(N)]).
show_rpil_op(var(N)) =
    string.format("v%d", [i(N)]).
show_rpil_op(place(Op, N)) =
    string.format("%s.p%d", [s(show_rpil_op(Op)), i(N)]).
show_rpil_op(place_ext(Op)) =
    string.format("%s.ext", [s(show_rpil_op(Op))]).
show_rpil_op(variant_place(Op, N1, N2)) =
    string.format("%s.v%dp%d", [s(show_rpil_op(Op)), i(N1), i(N2)]).
show_rpil_op(deref(Op)) =
    string.format("(%s)*", [s(show_rpil_op(Op))]).

show_rpil_inst(rpil_bind(Op1, Op2)) =
    string.format(
        "BIND %s, %s",
        [s(show_rpil_op(Op1)), s(show_rpil_op(Op2))]).
show_rpil_inst(rpil_move(Op)) =
    string.format("MOVE %s", [s(show_rpil_op(Op))]).
show_rpil_inst(rpil_borrow(Op1, Op2)) =
    string.format(
        "BORROW %s, %s",
        [s(show_rpil_op(Op1)), s(show_rpil_op(Op2))]).
show_rpil_inst(rpil_borrow_mut(Op1, Op2)) =
    string.format(
        "BORROW-MUT %s, %s",
        [s(show_rpil_op(Op1)), s(show_rpil_op(Op2))]).
show_rpil_inst(rpil_deref_move(Op)) =
    string.format("DEREF-MOVE %s", [s(show_rpil_op(Op))]).
show_rpil_inst(rpil_deref_pin(Op)) =
    string.format("DEREF-PIN %s", [s(show_rpil_op(Op))]).

show_rpil_insts(Insts) = string.join_list("\n", Reprs) :-
    Reprs = list.map(show_rpil_inst, Insts).

show_liveness(alive) = "alive".
show_liveness(dead) = "dead".

show_borrow_kind(shared) = "shared".
show_borrow_kind(mutable) = "mutable".

%---------------------------------------------------------------------------%
:- end_module pinchecker.
%---------------------------------------------------------------------------%
