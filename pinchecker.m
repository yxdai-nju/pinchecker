%---------------------------------------------------------------------------%
%
% File: pinchecker.m
% Version: 0.0.2
% Author: Yuxuan Dai <yxdai@smail.nju.edu.cn>
%
% This module provides an compilable implementation of PinChecker.
%
%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%

:- module pinchecker.
:- interface.

:- import_module io.

%---------------------------------------------------------------------------%

:- pred main(io::di, io::uo) is det.

%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%

:- implementation.

:- import_module list.
:- import_module require.
:- import_module string.

:- type rs_func
    --->    move_F
    ;       unmovable_new_F.

:- type rs_type
    --->    unmovable_T.

:- type rs_stmt
    --->    rs_stmt(
                line    :: int,
                fn      :: rs_func,
                args    :: list(int)
            ).

:- type rpil_op
    --->    arg(int)
    ;       var(int)
    ;       place(rpil_op, int)
    ;       place_ext(rpil_op)
    ;       variant_place(rpil_op, int, int)
    ;       deref(rpil_op).


:- type rpil_inst
    --->    rpil_bind(rpil_op, rpil_op)
    ;       rpil_move(rpil_op)
    ;       rpil_borrow(rpil_op, rpil_op)
    ;       rpil_borrow_mut(rpil_op, rpil_op)
    ;       rpil_deref_move(rpil_op)
    ;       rpil_deref_pin(rpil_op).

%---------------------------------------------------------------------------%

main(!IO) :-
    Stmts = [rs_stmt(2, move_F, [1]),
             rs_stmt(1, unmovable_new_F, [])],
    io.format("[Rust demo]\n%s\n", [s(debug_rs_stmts(Stmts))], !IO),
    Insts = fn_rpil_reduced(move_F, [2,1]),
    InstsRepr = debug_rpil_insts(Insts),
    io.format("\n[RPIL demo]\n%s\n", [s(InstsRepr)], !IO).

:- pred fn_typing(rs_func, list(rs_type), rs_type).
:- mode fn_typing(in, in, out) is semidet.
:- mode fn_typing(in, out, in) is det.

fn_typing(move_F, [T], T).
fn_typing(unmovable_new_F, [], unmovable_T).

:- func fn_rpil(rs_func) = list(rpil_inst).

fn_rpil(move_F) = [
    rpil_bind(arg(0),arg(1)),
    rpil_move(arg(1))].
fn_rpil(unmovable_new_F) = [].

    % Reduces the RPIL (Reference Provenance Intermediate Language)
    % instructions for a given function
    %
:- func fn_rpil_reduced(rs_func, list(int)) = list(rpil_inst).

fn_rpil_reduced(Func, Ops) = RpilReduced :-
    Rpil = fn_rpil(Func),
    RpilReduced = rpil_reduction(Ops, Rpil).

    % Reduces a list of RPIL instructions
    %
:- func rpil_reduction(list(int), list(rpil_inst)) = list(rpil_inst).

rpil_reduction(Ops, Rpil) = RpilReduced :-
    RpilReduced = list.map(rpil_inst_reduction(Ops), Rpil).

    % Reduces a single RPIL instruction
    %
:- func rpil_inst_reduction(list(int), rpil_inst) = rpil_inst.

rpil_inst_reduction(Ops, Inst) = InstReduced :-
    ( Inst = rpil_bind(Term1, Term2) ->
        TermReduced1 = rpil_term_reduction(Ops, Term1),
        TermReduced2 = rpil_term_reduction(Ops, Term2),
        InstReduced = rpil_bind(TermReduced1, TermReduced2)
    ; Inst = rpil_move(Term) ->
        TermReduced = rpil_term_reduction(Ops, Term),
        InstReduced = rpil_move(TermReduced)
    ; Inst = rpil_borrow(Term1, Term2) ->
        TermReduced1 = rpil_term_reduction(Ops, Term1),
        TermReduced2 = rpil_term_reduction(Ops, Term2),
        InstReduced = rpil_borrow(TermReduced1, TermReduced2)
    ; Inst = rpil_borrow_mut(Term1, Term2) ->
        TermReduced1 = rpil_term_reduction(Ops, Term1),
        TermReduced2 = rpil_term_reduction(Ops, Term2),
        InstReduced = rpil_borrow_mut(TermReduced1, TermReduced2)
    ; Inst = rpil_deref_move(Term) ->
        TermReduced = rpil_term_reduction(Ops, Term),
        InstReduced = rpil_deref_move(TermReduced)
    ; Inst = rpil_deref_pin(Term) ->
        TermReduced = rpil_term_reduction(Ops, Term),
        InstReduced = rpil_deref_pin(TermReduced)
    ;
        unexpected($pred, "unknown RPIL instruction")
    ).

    % Reduces a term in an RPIL instruction
    %
:- func rpil_term_reduction(list(int), rpil_op) = rpil_op.

rpil_term_reduction(Ops, Term) = TermReduced :-
    ( Term = arg(Idx) ->
        ( list.index0(Ops, Idx, Var) ->
            TermReduced = var(Var)
        ;
            unexpected($pred, "invalid index")
        )
    ; Term = var(_) ->
        unexpected($pred, "cannot reduce a reduced RPIL operator")
    ; Term = place(InnerTerm, P) ->
        InnerTermReduced = rpil_term_reduction(Ops, InnerTerm),
        TermReduced = place(InnerTermReduced, P)
    ; Term = place_ext(InnerTerm) ->
        InnerTermReduced = rpil_term_reduction(Ops, InnerTerm),
        TermReduced = place_ext(InnerTermReduced)
    ; Term = variant_place(InnerTerm, V, P) ->
        InnerTermReduced = rpil_term_reduction(Ops, InnerTerm),
        TermReduced = variant_place(InnerTermReduced, V, P)
    ; Term = deref(InnerTerm) ->
        InnerTermReduced = rpil_term_reduction(Ops, InnerTerm),
        TermReduced = deref(InnerTermReduced)
    ;
        unexpected($pred, "unknown RPIL operator")
    ).

%---------------------------------------------------------------------------%
%
% Convert rs_* structures to string representations for debugging purposes.
%

:- func debug_rs_func(rs_func) = string.

debug_rs_func(Func) = Repr :-
    ( Func = move_F ->
        Repr = "move"
    ; Func = unmovable_new_F ->
        Repr = "Unmovable::new"
    ;
        unexpected($pred, "unknown Rust function")
    ).

:- func debug_rs_stmt(rs_stmt) = string.

debug_rs_stmt(Stmt) = Repr :-
    Stmt = rs_stmt(Line, Func, Args),
    FuncRepr = debug_rs_func(Func),
    list.map(
        (pred(Arg::in, ArgStr::out) is det :-
            string.format("v%d", [i(Arg)], ArgStr)),
        Args,
        ArgStrs),
    ArgsRepr = string.join_list(", ", ArgStrs),
    string.format(
        "let v%d = %s(%s);",
        [i(Line), s(FuncRepr), s(ArgsRepr)],
        Repr).

:- func debug_rs_stmts(list(rs_stmt)) = string.

debug_rs_stmts(Stmts) = Repr :-
    RevReprs = list.map(debug_rs_stmt, Stmts),
    Reprs = list.reverse(RevReprs),
    Repr = string.join_list("\n", Reprs).

:- func debug_rpil_op(rpil_op) = string.

debug_rpil_op(Op) = Repr :-
    ( Op = arg(N) ->
        string.format("_%d", [i(N)], Repr)
    ; Op = var(N) ->
        string.format("v%d", [i(N)], Repr)
    ; Op = place(InnerOp, N) ->
        InnerRepr = debug_rpil_op(InnerOp),
        string.format("%s.p%d", [s(InnerRepr), i(N)], Repr)
    ; Op = place_ext(InnerOp) ->
        InnerRepr = debug_rpil_op(InnerOp),
        string.format("%s.ext", [s(InnerRepr)], Repr)
    ; Op = variant_place(InnerOp, N1, N2) ->
        InnerRepr = debug_rpil_op(InnerOp),
        string.format("%s.v%dp%d", [s(InnerRepr), i(N1), i(N2)], Repr)
    ; Op = deref(InnerOp) ->
        InnerRepr = debug_rpil_op(InnerOp),
        string.format("(%s)*", [s(InnerRepr)], Repr)
    ;
        unexpected($pred, "unknown RPIL operator")
    ).

:- func debug_rpil_inst(rpil_inst) = string.

debug_rpil_inst(Inst) = Repr :-
    ( Inst = rpil_bind(Op1, Op2) ->
        Repr1 = debug_rpil_op(Op1),
        Repr2 = debug_rpil_op(Op2),
        string.format("BIND %s, %s", [s(Repr1), s(Repr2)], Repr)
    ; Inst = rpil_move(Op) ->
        OpRepr = debug_rpil_op(Op),
        string.format("MOVE %s", [s(OpRepr)], Repr)
    ; Inst = rpil_borrow(Op1, Op2) ->
        Repr1 = debug_rpil_op(Op1),
        Repr2 = debug_rpil_op(Op2),
        string.format("BORROW %s, %s", [s(Repr1), s(Repr2)], Repr)
    ; Inst = rpil_borrow_mut(Op1, Op2) ->
        Repr1 = debug_rpil_op(Op1),
        Repr2 = debug_rpil_op(Op2),
        string.format("BORROW-MUT %s, %s", [s(Repr1), s(Repr2)], Repr)
    ; Inst = rpil_deref_move(Op) ->
        OpRepr = debug_rpil_op(Op),
        string.format("DEREF-MOVE %s", [s(OpRepr)], Repr)
    ; Inst = rpil_deref_pin(Op) ->
        OpRepr = debug_rpil_op(Op),
        string.format("DEREF-PIN %s", [s(OpRepr)], Repr)
    ;
        unexpected($pred, "unknown RPIL instruction")
    ).

:- func debug_rpil_insts(list(rpil_inst)) = string.

debug_rpil_insts(Insts) = Repr :-
    Reprs = list.map(debug_rpil_inst, Insts),
    Repr = string.join_list("\n", Reprs).

%---------------------------------------------------------------------------%
:- end_module pinchecker.
%---------------------------------------------------------------------------%
