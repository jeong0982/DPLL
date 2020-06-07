from collections import deque
import operator

class Solver:

    def __init__(self, filename):
        self.filename = filename
        self.clauses, self.vars = Solver.read_file(filename)
        self.learnts = set()
        self.assigns = dict.fromkeys(list(self.vars), -1)
        self.level = 0
        self.nodes = dict((var, Node(var, -1)) for var in list(self.vars))
        self.branching_vars = set()
        self.branching_history = {}  # level -> branched variable
        self.propagate_history = {}  # level -> propagate variables list
        self.branching_count = 0
        
    def read_file(filename):
        with open(filename) as f:
            lines = [
                line.strip().split() for line in f.readlines()
                if (not (line.startswith('c') or
                         line.startswith('%') or
                         line.startswith('0'))
                    and line != '\n')
            ]

        literals = set()
        clauses = set()

        for line in lines[1:]:
            clause = frozenset(map(int, line[:-1]))
            literals.update(map(abs, clause))
            clauses.add(clause)

        return clauses, literals

    def solve(self):
        while not self.are_all_variables_assigned():
            conf_cls = self.unit_propagate()
            if conf_cls is not None:
                lvl, learnt = self.conflict_analyze(conf_cls)
                if lvl < 0:
                    return False
                self.learnts.add(learnt)
                self.backtrack(lvl)
                self.level = lvl
            elif self.are_all_variables_assigned():
                break
            else:
                self.level += 1
                self.branching_count += 1
                bt_var, bt_val = self.pick_branching_variable()
                self.assigns[bt_var] = bt_val
                self.branching_vars.add(bt_var)
                self.branching_history[self.level] = bt_var
                self.propagate_history[self.level] = deque()
                self.set_node(bt_var)
        return True

    def set_node(self, var):
        node = self.nodes[var]
        node.value = self.assigns[var]
        node.level = self.level

    def update_graph(self, var, clause):
        node = self.nodes[var]
        self.set_node(var)
        for v in [abs(lit) for lit in clause if abs(lit) != var]:
            node.parents.append(self.nodes[v])
            self.nodes[v].children.append(node)
        node.clause = clause

    def all_unassigned_vars(self):
        return filter(
            lambda v: v in self.assigns and self.assigns[v] == -1,
            self.vars)

    def all_unresolved_clauses(self):
        return filter(lambda c: self.compute_clause(c) == -1, self.clauses)

    def pick_branching_variable(self):
        positive = {x: 0 for x in self.vars if self.assigns[x] == -1}
        negative = {x: 0 for x in self.vars if self.assigns[x] == -1}
        for clause in self.all_unresolved_clauses():
            for v in clause:
                try:
                    if v > 0:
                        positive[v] += 1
                    else:
                        negative[abs(v)] += 1
                except KeyError:
                    pass
        pos_count = max(positive.items(), key = operator.itemgetter(1))
        neg_count = max(negative.items(), key = operator.itemgetter(1))
        if pos_count[1] > neg_count[1]:
            return pos_count[0], 1
        else:
            return neg_count[0], 0

    def are_all_variables_assigned(self):
        for var in self.vars:
            if not var in self.assigns:
                return False
        for var in self.vars:
            if self.assigns[var] == -1:
                return False
        return True

    def compute_clause(self, clause):
        values = []
        for var in clause:
            value = self.assigns[abs(var)]
            if value == -1:
                values.append(-1)
            else:
                if var < 0:
                    if value == 1:
                        values.append(0)
                    else:
                        values.append(1)
                else:
                    if value == 0:
                        values.append(0)
                    else:
                        values.append(1)
        if -1 in values:
            return -1
        else:
            return max(values)

    def compute_value(self, var):
        value = self.assigns[abs(var)]
        value = value if value == -1 else value ^ (var < 0)
        return value

    def is_unit_clause(self, clause):
        values = []
        unassigned = None

        for literal in clause:
            value = self.compute_value(literal)
            values.append(value)
            unassigned = literal if value == -1 else unassigned

        check = ((values.count(0) == len(clause) - 1 and
                  values.count(-1) == 1) or
                 (len(clause) == 1
                  and values.count(-1) == 1))

        return check, unassigned

    def unit_propagate(self):
        while True:
            propagate_queue = deque()
            all_clauses = list(self.clauses.union(self.learnts))
            for clause in all_clauses:
                val = self.compute_clause(clause)
                if val == 1:
                    continue
                if val == 0:
                    return clause
                else:
                    is_unit, unit_literal = self.is_unit_clause(clause)
                    if not is_unit:
                        continue
                    prop_pair = (unit_literal, clause)
                    if prop_pair not in propagate_queue:
                        propagate_queue.append(prop_pair)
            if not propagate_queue:
                return None

            for prop_literal, clause in propagate_queue:
                prop_var = abs(prop_literal)
                if prop_literal > 0:
                    self.assigns[prop_var] = 1
                else:
                    self.assigns[prop_var] = 0
                self.update_graph(prop_var, clause)
                try:
                    self.propagate_history[self.level].append(prop_literal)
                except KeyError:
                    pass

    def conflict_analyze(self, conf_clause):

        if self.level == 0:
            return -1, None
        assign_history = [self.branching_history[self.level]] + list(self.propagate_history[self.level])

        conf_literals = conf_clause
        done_literals = set()
        curr_level_literals = set()
        prev_level_literals = set()

        while True:
            for var in conf_literals:
                if self.nodes[abs(var)].level == self.level:
                    curr_level_literals.add(var)
                else:
                    prev_level_literals.add(var)

            if len(curr_level_literals) == 1:
                break

            for v in reversed(assign_history):
                if v in curr_level_literals or -v in curr_level_literals:
                    last_assigned, others = v, [x for x in curr_level_literals if abs(x) != abs(v)]

            done_literals.add(abs(last_assigned))
            curr_level_literals = set(others)

            pool_clause = self.nodes[abs(last_assigned)].clause
            conf_literals = [
                l for l in pool_clause if abs(l) not in done_literals
            ] if pool_clause is not None else []

        learnt = frozenset([l for l in curr_level_literals.union(prev_level_literals)])
        if prev_level_literals:
            level = max([self.nodes[abs(x)].level for x in prev_level_literals])
        else:
            level = self.level - 1
        print(level, learnt)
        return level, learnt

    def backtrack(self, level):
        for var, node in self.nodes.items():
            if node.level <= level:
                node.children[:] = [child for child in node.children if child.level <= level]
            else:
                node.value = -1
                node.level = -1
                node.parents = []
                node.children = []
                node.clause = None
                self.assigns[node.variable] = -1

        self.branching_vars = set([
            var for var in self.vars
            if (self.assigns[var] != -1
                and len(self.nodes[var].parents) == 0)
        ])

        levels = list(self.propagate_history.keys())
        for k in levels:
            if k <= level:
                continue
            del self.branching_history[k]
            del self.propagate_history[k]

class Node:
    def __init__(self, variable, value):
        self.variable = variable
        self.value = value
        self.level = -1
        self.parents = []
        self.children = []
        self.clause = None

for i in range(10):
    index = i + 1
    st = 'cnf/uf75-0%d.cnf' % index
    s = Solver(st)
    print(s.solve())