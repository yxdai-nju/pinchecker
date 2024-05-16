from pprint import pformat
from sympy.unify.core import Variable, unify
from collections import deque

MAX_TYPE_SIZE = 5

fn_tmps = {
    "deref_move": (
        1,
        lambda t1: (
            (
                "[multiarg]",
                ("Pin", ("Box", t1)),
                ("DroppingSlot", ("Box", ("MaybeUninit", t1))),
            ),
            ("MoveRef", t1),
        ),
    ),
    "deref_mut": (1, lambda t1: (("MoveRef", t1), ("MutRef", t1))),
    "Box::pin": (1, lambda t1: ("[noarg]", ("Pin", ("Box", t1)))),
    "borrow_mut": (1, lambda t1: (t1, ("MutRef", t1))),
    "SlotDropper::new": (1, lambda t1: ("[noarg]", ("SlotDropper", t1))),
    "new_unchecked_hygine_hack": (
        1,
        lambda t1: (
            ("MutRef", ("SlotDropper", t1)),
            ("DroppingSlot", t1),
        ),
    ),
}


def fn_varify(fn_id):
    tyvar_count, fn_tmp = fn_tmps[fn_id]
    tyvars = tuple(Variable("T%d" % (i,)) for i in range(1, tyvar_count + 1))
    return (tyvars, fn_tmp(*tyvars))


def fn_varify_with_unification_results(fn_id, tyvars, unification):
    _, fn_tmp = fn_tmps[fn_id]
    unified_tyvars = tuple(
        (unification[tv] if tv in unification else tv) for tv in tyvars
    )
    return (unified_tyvars, fn_tmp(*unified_tyvars))


def fn_tyargs(fn_varified_tmp):
    if isinstance(fn_varified_tmp[0], tuple) and fn_varified_tmp[0][0] == "[multiarg]":
        tyargs = fn_varified_tmp[0][1:]
    else:
        tyargs = (fn_varified_tmp[0],)
    return tyargs


def fn_tyret(fn_varified_tmp):
    return fn_varified_tmp[1]


class Goal:
    def __init__(self, goal, parent_id):
        self.goal = goal
        self.parent_id = parent_id
        self.merge_method = None
        self.subgoal_ids = None
        self.remaining_subgoals = None
        self.result = None

    def init(self, merge_method, subgoal_ids):
        self.merge_method = merge_method
        self.subgoal_ids = subgoal_ids
        self.remaining_subgoals = len(subgoal_ids)

    def merge(self, subgoal_result):
        self.remaining_subgoals -= 1
        if self.merge_method == "and":
            if subgoal_result is False:
                self.result = False
                return False
            if self.remaining_subgoals == 0:
                self.result = True
                return True
        elif self.merge_method == "or":
            if subgoal_result is True:
                self.result = True
                return True
            if self.remaining_subgoals == 0:
                self.result = False
                return False
        return None

    def __repr__(self):
        attrs = [
            "goal",
            "parent_id",
            "merge_method",
            "subgoal_ids",
            "remaining_subgoals",
            "result",
        ]
        s = ["%s: %s" % (attr, pformat(self.__dict__[attr])) for attr in attrs]
        return "Goal {\n    " + "\n    ".join(s) + "\n}"


def type_size(ty):
    if isinstance(ty, tuple):
        size = 0
        for item in ty:
            size += type_size(item)
        return size
    return 1


class Solver:
    def __init__(self):
        self.next_goal_id = 0
        self.goal_map = {}
        self.goals = deque()
        self.solved_goal_ids = set()
        self.from_reachability = set()
        self.reachability = set()
        self.solved = False

    def solve(self, goal):
        self.next_goal_id = 0
        self.goal_map.clear()
        self.solved = False
        self.add_goal(goal=goal, parent_id=None)
        while not self.solved:
            self.step()

    def memorize(self, solved_goal):
        goal_type, *goal_args = solved_goal
        if goal_type == "reachable-from":
            (ty_from, ty_to) = goal_args
            self.from_reachability.add((ty_from, ty_to))
            self.reachability.add(ty_to)
        if goal_type == "reachable":
            (ty_to,) = goal_args
            self.reachability.add(ty_to)

    def mark_goal_as_solved(self, goal_id):
        goal: Goal = self.goal_map[goal_id]
        subgoal_ids = goal.subgoal_ids
        if subgoal_ids is not None:
            self.solved_goal_ids.update(subgoal_ids)
            for subgoal_id in subgoal_ids:
                self.mark_goal_as_solved(subgoal_id)

    def merge_goal_to_parent(self, goal_id, goal_result):
        assert goal_result is not None
        goal: Goal = self.goal_map[goal_id]
        if goal.parent_id is None:
            self.solved = True
            return
        parent_goal: Goal = self.goal_map[goal.parent_id]
        merge_result = parent_goal.merge(goal_result)
        if merge_result is not None:
            if merge_result is True:
                self.memorize(parent_goal.goal)
            self.mark_goal_as_solved(goal.parent_id)
            self.merge_goal_to_parent(goal.parent_id, merge_result)

    def add_goal(self, goal, parent_id):
        goal_id = self.next_goal_id
        self.next_goal_id += 1
        self.goal_map[goal_id] = Goal(
            goal=goal,
            parent_id=parent_id,
        )
        self.goals.append(goal_id)
        return goal_id

    def init_goal(self, goal_id, merge_method, subgoal_ids):
        goal = self.goal_map[goal_id]
        goal.init(merge_method, subgoal_ids)

    def step_reachable_from(self, goal_id, ty_from, ty_to):
        if (
            ty_to == "[noarg]"
            or ty_from == ty_to
            or (ty_from, ty_to) in self.from_reachability
        ):
            self.merge_goal_to_parent(goal_id, goal_result=True)
            return
        if type_size(ty_to) > MAX_TYPE_SIZE:  # limit search size
            self.merge_goal_to_parent(goal_id, goal_result=False)
            return
        subgoal_ids = []
        for fn_id in fn_tmps:
            tyvars, (fn_varified_ty_from, fn_varified_ty_to) = fn_varify(fn_id)
            for u in unify(ty_to, fn_varified_ty_to):
                _, unified_fn_tmp = fn_varify_with_unification_results(
                    fn_id, tyvars=tyvars, unification=u
                )
                tyargs = set(fn_tyargs(unified_fn_tmp))
                if len(tyargs) == 1:
                    tyarg = tyargs.pop()
                    if tyarg == ty_to:  # prune infinite recursion
                        continue
                    subgoal_id = self.add_goal(
                        goal=("reachable-from", ty_from, tyarg),
                        parent_id=goal_id,
                    )
                    subgoal_ids.append(subgoal_id)
                else:  # [multiarg]
                    tyargs = list(tyargs)
                    for head_idx in range(len(tyargs)):
                        ty_head, ty_tail = tyargs[head_idx], [
                            tyarg for i, tyarg in enumerate(tyargs) if i != head_idx
                        ]
                        if ty_head == ty_to:  # prune infinite recursion
                            continue
                        subgoal_id = self.add_goal(
                            goal=("multiarg-reachable-from", ty_from, ty_head, ty_tail),
                            parent_id=goal_id,
                        )
                        subgoal_ids.append(subgoal_id)
        if len(subgoal_ids) > 0:
            self.init_goal(goal_id, "or", subgoal_ids)
        else:
            self.merge_goal_to_parent(goal_id, goal_result=False)

    def step_reachable(self, goal_id, ty_to):
        if ty_to == "[noarg]" or ty_to in self.reachability:
            self.merge_goal_to_parent(goal_id, goal_result=True)
            return
        if type_size(ty_to) > MAX_TYPE_SIZE:  # limit search size
            self.merge_goal_to_parent(goal_id, goal_result=False)
            return
        subgoal_ids = []
        for fn_id in fn_tmps:
            tyvars, (fn_varified_ty_from, fn_varified_ty_to) = fn_varify(fn_id)
            for u in unify(ty_to, fn_varified_ty_to):
                _, unified_fn_tmp = fn_varify_with_unification_results(
                    fn_id, tyvars=tyvars, unification=u
                )
                tyargs = set(fn_tyargs(unified_fn_tmp))
                if ty_to in tyargs:  # prune infinite recursion
                    continue
                for tyarg in tyargs:
                    subgoal_id = self.add_goal(
                        goal=("reachable", tyarg),
                        parent_id=goal_id,
                    )
                    subgoal_ids.append(subgoal_id)
        if len(subgoal_ids) > 0:
            self.init_goal(goal_id, "and", subgoal_ids)
        else:
            self.merge_goal_to_parent(goal_id, goal_result=False)

    def step_multiarg_reachable_from(self, goal_id, ty_from, ty_head, ty_tail):
        subgoal_ids = []
        subgoal_id = self.add_goal(
            goal=("reachable-from", ty_from, ty_head),
            parent_id=goal_id,
        )
        subgoal_ids.append(subgoal_id)
        for ty in ty_tail:
            subgoal_id = self.add_goal(
                goal=("reachable", ty),
                parent_id=goal_id,
            )
            subgoal_ids.append(subgoal_id)
        self.init_goal(goal_id, "and", subgoal_ids)

    def step(self):
        # for k, v in self.goal_map.items():
        #     print(k, v)
        goal_id = self.goals.popleft()
        if goal_id in self.solved_goal_ids:
            return
        goal_type, *goal_args = self.goal_map[goal_id].goal
        if goal_type == "reachable-from":
            (ty_from, ty_to) = goal_args
            self.step_reachable_from(goal_id, ty_from, ty_to)
        elif goal_type == "reachable":
            (ty_to,) = goal_args
            self.step_reachable(goal_id, ty_to)
        elif goal_type == "multiarg-reachable-from":
            (ty_from, ty_head, ty_tail) = goal_args
            self.step_multiarg_reachable_from(goal_id, ty_from, ty_head, ty_tail)

    def reachable(self, ty_from, ty_to):
        self.solve(goal=("reachable-from", ty_from, ty_to))
        return (ty_from, ty_to) in self.from_reachability


solver = Solver()
reachable = solver.reachable(
    ty_from=("Pin", ("Box", "Unmovable")),
    ty_to=("MutRef", "Unmovable"),
)


def ty_format(ty):
    if isinstance(ty, tuple):
        return f"{ty[0]}<{ty_format(ty[1])}>"
    return ty


print(reachable)
for ty_from, ty_to in solver.from_reachability:
    print(ty_format(ty_from), "->", ty_format(ty_to))
